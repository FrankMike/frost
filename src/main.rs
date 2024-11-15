//! Example usage of the FROST threshold signature scheme.

mod frost;

use frost::{
    generate_frost_keys, aggregate_signatures, verify_signature, 
    compute_group_public_key, aggregate_commitments,
    FrostError,
};

fn main() -> Result<(), FrostError> {
    // Define the threshold and number of participants
    let threshold = 3;
    let total_participants = 5;

    // Generate keys and shares for participants
    let participants = generate_frost_keys(threshold, total_participants)?;
    
    // Compute the group public key
    let group_public_key = compute_group_public_key(&participants);

    // Define a message to be signed
    let message = b"Hello, FROST!";

    // Use only threshold number of participants for signing
    let signing_participants = &participants[0..threshold];

    // Simulate the signing process
    let mut commitments = Vec::new();
    let mut secret_commitments = Vec::new();
    let mut signature_shares = Vec::new();

    // Each participant generates a commitment
    for participant in signing_participants {
        let (commitment, secret_commitment) = participant.generate_commitment();
        commitments.push(commitment);
        secret_commitments.push(secret_commitment);
    }

    // Get participant indices
    let participant_indices: Vec<u32> = signing_participants.iter()
        .map(|p| p.index)
        .collect();

    // Aggregate commitments to form the group commitment
    let group_commitment = aggregate_commitments(
        &commitments,
        message,
        &participant_indices,
        group_public_key,
    );

    // Each participant generates a signature share
    for (i, participant) in signing_participants.iter().enumerate() {
        let signature_share = participant.generate_signature_share(
            message,
            &group_commitment,
            secret_commitments[i],
            group_public_key,
        );
        signature_shares.push(signature_share);
    }

    // Aggregate signature shares into a complete signature
    let frost_signature = aggregate_signatures(
        &signature_shares,
        group_commitment.aggregated,
        message,
        group_public_key,
    )?;

    // Print debug information
    println!("Debug Info:");
    println!("Message: {:?}", message);
    println!("Group Public Key: {:?}", group_public_key);
    println!("Group Commitment: {:?}", group_commitment.aggregated);
    println!("Signature z: {:?}", frost_signature.z);
    println!("Signature c: {:?}", frost_signature.c);

    // Verify the signature
    let is_valid = verify_signature(
        &frost_signature,
        message,
        group_public_key,
    );

    if is_valid {
        println!("Signature is valid!");
    } else {
        println!("Signature is invalid!");
        println!("Group commitment: {:?}", group_commitment.aggregated);
        println!("Number of signature shares: {}", signature_shares.len());
    }

    Ok(())
}
