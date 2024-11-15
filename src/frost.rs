//! FROST: Flexible Round-Optimized Schnorr Threshold Signatures implementation.
//! Based on the paper by Chelsea Komlo and Ian Goldberg.

use curve25519_dalek::{RistrettoPoint, Scalar};
use rand::rngs::OsRng;
use sha2::{Digest, Sha512};
use thiserror::Error;
use rand_core::RngCore;

/// Errors that can occur during FROST operations
#[allow(dead_code)]
#[derive(Error, Debug)]
pub enum FrostError {
    /// Threshold is zero or greater than the total number of participants
    #[error("Invalid threshold or number of participants")]
    InvalidParameters,
    /// Not enough signature shares provided
    #[error("Invalid number of shares for signature")]
    InvalidShareCount,
    /// Duplicate participant indices detected
    #[error("Duplicate participant indices")]
    DuplicateParticipants,
}

/// Represents a participant in the FROST protocol
#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Participant {
    /// Index of the participant (non-zero)
    pub index: u32,
    /// Secret share of the participant
    secret_share: Scalar,
    /// Public verification share
    pub public_key: RistrettoPoint,
    /// Verification shares for other participants
    pub verification_shares: Vec<RistrettoPoint>,
}

/// Represents a FROST signature share from a single participant
#[derive(Clone, Debug)]
pub struct SignatureShare {
    /// Index of the participant who created this share
    pub participant_index: u32,
    /// The signature share value
    pub z_i: Scalar,
}

/// Complete FROST signature
#[derive(Clone, Debug)]
pub struct FrostSignature {
    /// Aggregated signature value
    pub z: Scalar,
    /// Challenge value
    pub c: Scalar,
}

/// Represents a commitment share from a single participant
#[derive(Clone, Debug)]
pub struct CommitmentShare {
    /// First commitment value
    pub first: RistrettoPoint,
    /// Second commitment value
    pub second: RistrettoPoint,
}

/// Represents the aggregated group commitment
#[derive(Clone, Debug)]
pub struct GroupCommitment {
    /// Aggregated commitment value
    pub aggregated: RistrettoPoint,
    /// Individual commitments
    pub individual_commitments: Vec<CommitmentShare>,
}

/// Generates polynomial coefficients for Shamir's Secret Sharing
fn generate_polynomial_coefficients(threshold: usize) -> Vec<Scalar> {
    let mut rng = OsRng;
    let mut coefficients = Vec::with_capacity(threshold);
    for _ in 0..threshold {
        let mut bytes = [0u8; 64];
        rng.fill_bytes(&mut bytes);
        coefficients.push(Scalar::from_bytes_mod_order_wide(&bytes));
    }
    coefficients
}

/// Evaluates polynomial at a given point
fn evaluate_polynomial(coefficients: &[Scalar], x: Scalar) -> Scalar {
    let mut result = Scalar::from(0u8);
    let mut x_pow = Scalar::from(1u8);
    
    for coeff in coefficients {
        result += *coeff * x_pow;
        x_pow *= x;
    }
    result
}

impl Participant {
    /// Creates a new participant with their secret share
    pub fn new(
        index: u32,
        secret_share: Scalar,
        public_key: RistrettoPoint,
        verification_shares: Vec<RistrettoPoint>,
    ) -> Self {
        Self {
            index,
            secret_share,
            public_key,
            verification_shares,
        }
    }

    /// Generates a commitment for the first round of signing
    pub fn generate_commitment(&self) -> (CommitmentShare, (Scalar, Scalar)) {
        let mut rng = OsRng;
        let mut bytes = [0u8; 64];
        
        // Generate two random values
        rng.fill_bytes(&mut bytes);
        let d = Scalar::from_bytes_mod_order_wide(&bytes);
        rng.fill_bytes(&mut bytes);
        let e = Scalar::from_bytes_mod_order_wide(&bytes);
        
        // Compute commitment share
        let first = RistrettoPoint::mul_base(&d);
        let second = RistrettoPoint::mul_base(&e);
        
        (CommitmentShare { first, second }, (d, e))
    }

    /// Generates a signature share for the second round of signing
    pub fn generate_signature_share(
        &self,
        message: &[u8],
        group_commitment: &GroupCommitment,
        secret_commitments: (Scalar, Scalar),
        group_public_key: RistrettoPoint,
    ) -> SignatureShare {
        let (d_i, e_i) = secret_commitments;
        
        // Compute binding factor
        let rho_i = compute_binding_factor(
            message,
            &group_commitment.individual_commitments[self.index as usize - 1].first,
            self.index,
            group_public_key,
        );
        
        // Compute challenge
        let c = compute_challenge(message, group_commitment.aggregated, group_public_key);
        
        // Compute signature share without Lagrange coefficient
        let z_i = d_i + (e_i * rho_i) + (self.secret_share * c);
        
        SignatureShare {
            participant_index: self.index,
            z_i,
        }
    }
}

/// Aggregates signature shares into a complete FROST signature
pub fn aggregate_signatures(
    shares: &[SignatureShare],
    commitment: RistrettoPoint,
    message: &[u8],
    group_public_key: RistrettoPoint,
) -> Result<FrostSignature, FrostError> {
    if shares.is_empty() {
        return Err(FrostError::InvalidShareCount);
    }

    // Extract participant indices
    let indices: Vec<u32> = shares.iter()
        .map(|share| share.participant_index)
        .collect();

    // Compute challenge
    let c = compute_challenge(message, commitment, group_public_key);

    // Compute Lagrange coefficients and multiply with shares
    let z = shares.iter()
        .map(|share| {
            let lambda_i = lagrange_coefficient(share.participant_index, &indices);
            share.z_i * lambda_i
        })
        .sum();

    Ok(FrostSignature { z, c })
}

/// Verifies a FROST signature
#[allow(non_snake_case)]
pub fn verify_signature(
    signature: &FrostSignature,
    message: &[u8],
    group_public_key: RistrettoPoint,
) -> bool {
    // Compute R = zG - cY where G is the base point and Y is the group public key
    let zG = RistrettoPoint::mul_base(&signature.z);
    let cY = group_public_key * signature.c;
    let R = zG - cY;
    
    // Recompute the challenge
    let c_verify = compute_challenge(message, R, group_public_key);
    
    // Add debug output
    println!("\nVerification Debug:");
    println!("zG: {:?}", zG);
    println!("cY: {:?}", cY);
    println!("R: {:?}", R);
    println!("c: {:?}", signature.c);
    println!("c_verify: {:?}", c_verify);
    
    signature.c == c_verify
}

/// Computes the challenge for the Schnorr signature
fn compute_challenge(message: &[u8], commitment: RistrettoPoint, public_key: RistrettoPoint) -> Scalar {
    let mut hasher = Sha512::new();
    // Add domain separation
    hasher.update(b"FROST_SIGNATURE");
    // Add commitment point
    hasher.update(commitment.compress().as_bytes());
    // Add public key
    hasher.update(public_key.compress().as_bytes());
    // Add message
    hasher.update(message);
    
    let hash = hasher.finalize();
    let mut hash_bytes = [0u8; 64];
    hash_bytes.copy_from_slice(&hash);
    Scalar::from_bytes_mod_order_wide(&hash_bytes)
}

/// Computes the group public key from participant public keys
pub fn compute_group_public_key(participants: &[Participant]) -> RistrettoPoint {
    // The group public key should be the sum of all verification shares[0]
    // This represents g^(f(0)) where f(0) is the secret key
    participants.iter()
        .map(|p| p.verification_shares[0])
        .sum()
}

/// Computes the Lagrange coefficient for a given participant
fn lagrange_coefficient(i: u32, indices: &[u32]) -> Scalar {
    let x_i = Scalar::from(i as u64);
    let mut numerator = Scalar::ONE;
    let mut denominator = Scalar::ONE;

    for &j in indices {
        if j != i {
            let x_j = Scalar::from(j as u64);
            // λᵢ = ∏ⱼ≠ᵢ (xⱼ/(xⱼ-xᵢ))
            numerator *= x_j;
            denominator *= x_j - x_i;
        }
    }

    numerator * denominator.invert()
}

/// Generates keys and shares for all participants
pub fn generate_frost_keys(
    threshold: usize,
    total_participants: usize,
) -> Result<Vec<Participant>, FrostError> {
    if threshold == 0 || threshold > total_participants {
        return Err(FrostError::InvalidParameters);
    }

    let mut rng = OsRng;
    let mut bytes = [0u8; 64];
    rng.fill_bytes(&mut bytes);
    
    // Generate the master secret
    let master_secret = Scalar::from_bytes_mod_order_wide(&bytes);
    let coefficients = {
        let mut coeffs = vec![master_secret];
        coeffs.extend(generate_polynomial_coefficients(threshold - 1));
        coeffs
    };

    let mut participants = Vec::with_capacity(total_participants);

    // Generate shares for each participant
    for i in 0..total_participants {
        let index = (i + 1) as u32;
        let x = Scalar::from(index as u64);
        let secret_share = evaluate_polynomial(&coefficients, x);
        
        // Generate public key and verification shares
        let public_key = RistrettoPoint::mul_base(&secret_share);
        let mut verification_shares = Vec::new();
        
        for coeff in &coefficients {
            verification_shares.push(RistrettoPoint::mul_base(coeff));
        }

        participants.push(Participant::new(
            index,
            secret_share,
            public_key,
            verification_shares,
        ));
    }

    Ok(participants)
}

/// Computes the binding factor
fn compute_binding_factor(
    message: &[u8],
    commitment: &RistrettoPoint,
    participant_index: u32,
    group_public_key: RistrettoPoint,
) -> Scalar {
    let mut hasher = Sha512::new();
    hasher.update(b"FROST_BINDING");
    hasher.update(commitment.compress().as_bytes());
    hasher.update(group_public_key.compress().as_bytes());
    hasher.update(&participant_index.to_le_bytes());
    hasher.update(message);
    
    let hash = hasher.finalize();
    let mut hash_bytes = [0u8; 64];
    hash_bytes.copy_from_slice(&hash);
    Scalar::from_bytes_mod_order_wide(&hash_bytes)
}

/// Modified group commitment aggregation
pub fn aggregate_commitments(
    commitment_shares: &[CommitmentShare],
    message: &[u8],
    participant_indices: &[u32],
    group_public_key: RistrettoPoint,
) -> GroupCommitment {
    let binding_factors: Vec<_> = participant_indices.iter()
        .zip(commitment_shares.iter())
        .map(|(&index, share)| {
            compute_binding_factor(
                message,
                &share.first,
                index,
                group_public_key,
            )
        })
        .collect();

    let aggregated = commitment_shares.iter()
        .zip(binding_factors.iter())
        .map(|(share, &rho)| {
            share.first + (share.second * rho)
        })
        .sum();

    GroupCommitment { 
        aggregated,
        individual_commitments: commitment_shares.to_vec(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_key_generation() -> Result<(), FrostError> {
        let threshold = 3;
        let total_participants = 5;
        
        let participants = generate_frost_keys(threshold, total_participants)?;
        
        assert_eq!(participants.len(), total_participants);
        assert_eq!(participants[0].index, 1);
        assert_eq!(participants[4].index, 5);
        
        Ok(())
    }

    #[test]
    fn test_invalid_threshold() {
        let threshold = 6;
        let total_participants = 5;
        
        let result = generate_frost_keys(threshold, total_participants);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), FrostError::InvalidParameters));
    }

    #[test]
    fn test_zero_threshold() {
        let threshold = 0;
        let total_participants = 5;
        
        let result = generate_frost_keys(threshold, total_participants);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), FrostError::InvalidParameters));
    }

    #[test]
    fn test_signature_generation_and_verification() -> Result<(), FrostError> {
        // Setup
        let threshold = 3;
        let total_participants = 5;
        let message = b"Test message";
        
        // Generate keys
        let participants = generate_frost_keys(threshold, total_participants)?;
        let group_public_key = compute_group_public_key(&participants);
        
        // Generate commitments
        let signing_participants = &participants[0..threshold];
        let mut commitments = Vec::new();
        let mut secret_commitments = Vec::new();
        
        for participant in signing_participants {
            let (commitment, secret_commitment) = participant.generate_commitment();
            commitments.push(commitment);
            secret_commitments.push(secret_commitment);
        }
        
        let participant_indices: Vec<u32> = signing_participants.iter()
            .map(|p| p.index)
            .collect();
        
        // Aggregate commitments
        let group_commitment = aggregate_commitments(
            &commitments,
            message,
            &participant_indices,
            group_public_key,
        );
        
        // Generate signature shares
        let mut signature_shares = Vec::new();
        for (i, participant) in signing_participants.iter().enumerate() {
            let share = participant.generate_signature_share(
                message,
                &group_commitment,
                secret_commitments[i],
                group_public_key,
            );
            signature_shares.push(share);
        }
        
        println!("\nTest Debug Information:");
        println!("Threshold: {}", threshold);
        println!("Total Participants: {}", total_participants);
        println!("Message: {:?}", message);
        println!("Group Public Key: {:?}", group_public_key);
        
        // Print individual participant information
        for (i, participant) in signing_participants.iter().enumerate() {
            println!("\nParticipant {}:", i + 1);
            println!("Index: {}", participant.index);
            println!("Public Key: {:?}", participant.public_key);
            println!("Secret Share (hidden): [...]");
            println!("Verification Shares: {:?}", participant.verification_shares);
        }
        
        // Print commitment information
        println!("\nCommitment Information:");
        for (i, commitment) in commitments.iter().enumerate() {
            println!("Commitment {}: {:?}", i + 1, commitment);
        }
        println!("Group Commitment: {:?}", group_commitment.aggregated);
        
        // Print signature share information
        println!("\nSignature Share Information:");
        for share in &signature_shares {
            println!("Share from participant {}: {:?}", share.participant_index, share.z_i);
        }
        
        // Print final signature information
        let signature = aggregate_signatures(
            &signature_shares,
            group_commitment.aggregated,
            message,
            group_public_key,
        )?;
        
        println!("\nFinal Signature:");
        println!("z: {:?}", signature.z);
        println!("c: {:?}", signature.c);
        
        let is_valid = verify_signature(&signature, message, group_public_key);
        assert!(is_valid, "Signature verification failed");
        Ok(())
    }

    #[test]
    fn test_different_messages() -> Result<(), FrostError> {
        // Setup
        let threshold = 3;
        let total_participants = 5;
        let message1 = b"Test message 1";
        let message2 = b"Test message 2";
        
        // Generate keys
        let participants = generate_frost_keys(threshold, total_participants)?;
        let group_public_key = compute_group_public_key(&participants);
        
        // Generate signature for message1
        let signing_participants = &participants[0..threshold];
        let mut commitments = Vec::new();
        let mut secret_commitments = Vec::new();
        
        for participant in signing_participants {
            let (commitment, secret_commitment) = participant.generate_commitment();
            commitments.push(commitment);
            secret_commitments.push(secret_commitment);
        }
        
        let participant_indices: Vec<u32> = signing_participants.iter()
            .map(|p| p.index)
            .collect();
        
        let group_commitment = aggregate_commitments(
            &commitments,
            message1,
            &participant_indices,
            group_public_key,
        );
        
        let mut signature_shares = Vec::new();
        for (i, participant) in signing_participants.iter().enumerate() {
            let share = participant.generate_signature_share(
                message1,
                &group_commitment,
                secret_commitments[i],
                group_public_key,
            );
            signature_shares.push(share);
        }
        
        let signature = aggregate_signatures(
            &signature_shares,
            group_commitment.aggregated,
            message1,
            group_public_key,
        )?;
        
        // Verify signature with correct and incorrect messages
        assert!(verify_signature(&signature, message1, group_public_key));
        assert!(!verify_signature(&signature, message2, group_public_key));
        
        Ok(())
    }

    #[test]
    fn test_lagrange_coefficient() {
        let indices = vec![1, 2, 3];
        let coeff = lagrange_coefficient(1, &indices);
        assert!(coeff != Scalar::ZERO);
        
        // Test that the sum of Lagrange coefficients equals 1
        let sum: Scalar = indices.iter()
            .map(|&i| lagrange_coefficient(i, &indices))
            .sum();
        
        // Due to floating-point arithmetic, we check if the sum is close to 1
        assert_eq!(sum, Scalar::ONE);
    }

    #[test]
    fn test_empty_signature_shares() {
        let shares = Vec::new();
        let commitment = RistrettoPoint::default();
        let message = b"Test message";
        let public_key = RistrettoPoint::default();
        
        let result = aggregate_signatures(&shares, commitment, message, public_key);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), FrostError::InvalidShareCount));
    }
}
