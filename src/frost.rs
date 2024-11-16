//! FROST: Flexible Round-Optimized Schnorr Threshold Signatures implementation.
//! Based on the paper by Chelsea Komlo and Ian Goldberg.

use curve25519_dalek::{constants::RISTRETTO_BASEPOINT_POINT, ristretto::RistrettoPoint, scalar::Scalar};
use rand_core::OsRng;
use sha2::{Digest, Sha512};
use thiserror::Error;
use rand_core::RngCore;

#[allow(dead_code)]
#[derive(Error, Debug)]
pub enum FrostError {
    #[error("Invalid threshold or number of participants")]
    InvalidParameters,
    #[error("Invalid number of shares for signature")]
    InvalidShareCount,
    #[error("Duplicate participant indices")]
    DuplicateParticipants,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Participant {
    pub index: u32,
    secret_share: Scalar,
    pub public_key: RistrettoPoint,
    pub verification_shares: Vec<RistrettoPoint>,
}

#[derive(Clone, Debug)]
pub struct SignatureShare {
    pub participant_index: u32,
    pub z_i: Scalar,
}

#[derive(Clone, Debug)]
pub struct FrostSignature {
    pub z: Scalar,
    pub c: Scalar,
    pub commitment: RistrettoPoint,
}

#[derive(Clone, Debug)]
pub struct CommitmentShare {
    pub first: RistrettoPoint,
    pub second: RistrettoPoint,
}

#[derive(Clone, Debug)]
pub struct GroupCommitment {
    pub aggregated: RistrettoPoint,
    pub individual_commitments: Vec<CommitmentShare>,
}

fn compute_binding_factor(
    message: &[u8],
    commitment: &RistrettoPoint,
    index: u32,
    group_public_key: RistrettoPoint,
) -> Scalar {
    let mut hasher = Sha512::new();
    hasher.update(b"FROST_BINDING");
    hasher.update(message);
    hasher.update(commitment.compress().as_bytes());
    hasher.update(&index.to_le_bytes());
    hasher.update(group_public_key.compress().as_bytes());
    
    let hash = hasher.finalize();
    let mut hash_arr = [0u8; 64];
    hash_arr.copy_from_slice(&hash);
    let result = Scalar::from_bytes_mod_order_wide(&hash_arr);
    result
}

pub fn compute_group_public_key(participants: &[Participant]) -> RistrettoPoint {
    participants.iter()
        .map(|p| p.public_key)
        .sum()
}

pub fn aggregate_commitments(
    commitments: &[CommitmentShare],
    message: &[u8],
    participant_indices: &[u32],
    group_public_key: RistrettoPoint,
) -> GroupCommitment {
    let aggregated = commitments.iter().enumerate().map(|(i, comm)| {
        let rho_i = compute_binding_factor(
            message,
            &comm.first,
            participant_indices[i],
            group_public_key,
        );
        comm.first + (comm.second * rho_i)
    }).sum();

    GroupCommitment {
        aggregated,
        individual_commitments: commitments.to_vec(),
    }
}

fn generate_polynomial_coefficients(threshold: usize) -> Vec<Scalar> {
    let mut rng = OsRng;
    (0..threshold)
        .map(|_| {
            let mut bytes = [0u8; 64];
            rng.fill_bytes(&mut bytes);
            Scalar::from_bytes_mod_order_wide(&bytes)
        })
        .collect()
}

fn evaluate_polynomial(coefficients: &[Scalar], x: Scalar) -> Scalar {
    coefficients.iter().rev().fold(Scalar::from_bytes_mod_order([0u8; 32]), |acc, coeff| acc * x + coeff)
}

impl Participant {
    pub fn new(index: u32, secret_share: Scalar, public_key: RistrettoPoint, verification_shares: Vec<RistrettoPoint>) -> Self {
        Self {
            index,
            secret_share,
            public_key,
            verification_shares,
        }
    }

    pub fn generate_commitment(&self) -> (CommitmentShare, (Scalar, Scalar)) {
        let mut rng = OsRng;
        let d = Scalar::from_bytes_mod_order_wide(&{
            let mut bytes = [0u8; 64];
            rng.fill_bytes(&mut bytes);
            bytes
        });
        let e = Scalar::from_bytes_mod_order_wide(&{
            let mut bytes = [0u8; 64];
            rng.fill_bytes(&mut bytes);
            bytes
        });
        
        let first = RISTRETTO_BASEPOINT_POINT * d;
        let second = RISTRETTO_BASEPOINT_POINT * e;

        (CommitmentShare { first, second }, (d, e))
    }

    pub fn generate_signature_share(
        &self,
        message: &[u8],
        group_commitment: &GroupCommitment,
        secret_commitments: (Scalar, Scalar),
        group_public_key: RistrettoPoint,
    ) -> SignatureShare {
        let (d_i, e_i) = secret_commitments;
        
        let rho_i = compute_binding_factor(
            message,
            &group_commitment.individual_commitments[self.index as usize - 1].first,
            self.index,
            group_public_key,
        );
        
        let c = compute_challenge(message, group_commitment.aggregated, group_public_key);
        
        let z_i = d_i + (e_i * rho_i) + (c * self.secret_share);
        
        SignatureShare {
            participant_index: self.index,
            z_i,
        }
    }
}

pub fn aggregate_signatures(
    shares: &[SignatureShare],
    commitment: RistrettoPoint,
    message: &[u8],
    group_public_key: RistrettoPoint,
) -> Result<FrostSignature, FrostError> {
    if shares.is_empty() {
        return Err(FrostError::InvalidShareCount);
    }

    let indices: Vec<u32> = shares.iter().map(|share| share.participant_index).collect();
    
    // First compute the challenge using the original commitment
    let c = compute_challenge(message, commitment, group_public_key);
    
    // Then compute z = Σ(z_i * λ_i)
    let z = shares.iter()
        .map(|share| {
            let lambda_i = lagrange_coefficient(share.participant_index, &indices);
            share.z_i * lambda_i
        })
        .sum();
    
    Ok(FrostSignature { z, c, commitment })
}

#[allow(non_snake_case)]
pub fn verify_signature(
    signature: &FrostSignature,
    message: &[u8],
    group_public_key: RistrettoPoint,
) -> bool {
    
    // Use the stored commitment to compute the challenge
    let c_verify = compute_challenge(message, signature.commitment, group_public_key);
    
    // Verify that R = zG - cY
    let R = (RISTRETTO_BASEPOINT_POINT * signature.z) - (group_public_key * signature.c);
    
    // Both conditions must be met:
    // 1. The challenges must match
    // 2. The commitment point must match R
    signature.c == c_verify && R == signature.commitment
}

fn compute_challenge(message: &[u8], commitment: RistrettoPoint, public_key: RistrettoPoint) -> Scalar {
    
    let mut hasher = Sha512::new();
    hasher.update(b"FROST_SIGNATURE");
    hasher.update(message);
    hasher.update(commitment.compress().as_bytes());
    hasher.update(public_key.compress().as_bytes());

    let hash = hasher.finalize();
    let mut hash_arr = [0u8; 64];
    hash_arr.copy_from_slice(&hash);
    let result = Scalar::from_bytes_mod_order_wide(&hash_arr);
    result
}

fn lagrange_coefficient(i: u32, indices: &[u32]) -> Scalar {
    let x_i = Scalar::from(i as u64);
    
    indices.iter()
        .filter(|&&j| j != i)
        .fold(Scalar::ONE, |acc, &j| {
            let x_j = Scalar::from(j as u64);
            // Calculate (x_j / (x_j - x_i))
            acc * (x_j * (x_j - x_i).invert())
        })
}

pub fn generate_frost_keys(
    threshold: usize,
    total_participants: usize,
) -> Result<Vec<Participant>, FrostError> {
    if threshold == 0 || threshold > total_participants {
        return Err(FrostError::InvalidParameters);
    }

    let master_secret = Scalar::from_bytes_mod_order_wide(&{
        let mut bytes = [0u8; 64];
        OsRng.fill_bytes(&mut bytes);
        bytes
    });
    let coefficients = {
        let mut coeffs = vec![master_secret];
        coeffs.extend(generate_polynomial_coefficients(threshold - 1));
        coeffs
    };

    let participants = (0..total_participants)
        .map(|i| {
            let index = (i + 1) as u32;
            let x = Scalar::from(index as u64);
            let secret_share = evaluate_polynomial(&coefficients, x);
            let public_key = RISTRETTO_BASEPOINT_POINT * secret_share;
            let verification_shares = coefficients
                .iter()
                .map(|coeff| RISTRETTO_BASEPOINT_POINT * coeff)
                .collect();

            Participant::new(index, secret_share, public_key, verification_shares)
        })
        .collect();

    Ok(participants)
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
        
        // println!("\nTest Debug Information:");
        // println!("Threshold: {}", threshold);
        // println!("Total Participants: {}", total_participants);
        // println!("Message: {:?}", message);
        // println!("Group Public Key: {:?}", group_public_key);
        
        // Print individual participant information
        // for (i, participant) in signing_participants.iter().enumerate() {
        //     println!("\nParticipant {}:", i + 1);
        //     println!("Index: {}", participant.index);
        //     println!("Public Key: {:?}", participant.public_key);
        //     println!("Secret Share (hidden): [...]");
        //     println!("Verification Shares: {:?}", participant.verification_shares);
        // }
        
        // Print commitment information
        // println!("\nCommitment Information:");
        // for (i, commitment) in commitments.iter().enumerate() {
        //     println!("Commitment {}: {:?}", i + 1, commitment);
        // }
        // println!("Group Commitment: {:?}", group_commitment.aggregated);
        
        // // Print signature share information
        // println!("\nSignature Share Information:");
        // for share in &signature_shares {
        //     println!("Share from participant {}: {:?}", share.participant_index, share.z_i);
        // }
        
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
        println!("Signature verification result: {}", is_valid);
        if !is_valid {
            println!("Signature verification failed");
        }
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
