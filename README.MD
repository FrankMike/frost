# FROST: Flexible Round-Optimized Schnorr Threshold Signatures

This is a Rust implementation of FROST (Flexible Round-Optimized Schnorr Threshold Signatures) based on the [paper by Chelsea Komlo and Ian Goldberg](https://eprint.iacr.org/2020/852.pdf).

## Overview

FROST is a threshold signature scheme that allows a group of participants to collectively create Schnorr signatures. It requires only two rounds of communication and provides better security properties compared to previous threshold Schnorr signature schemes.

Key features:
- Threshold signatures (t-of-n signing)
- Two-round signing protocol
- Based on Schnorr signatures
- Uses curve25519-dalek for cryptographic operations

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
curve25519-dalek = "4.0"
rand = "0.8"
rand_core = "0.6"
sha2 = "0.10"
thiserror = "2.0"
itertools = "0.13"
```

## Basic example:

```rust
use frost::{generate_frost_keys, aggregate_signatures, verify_signature,
compute_group_public_key, aggregate_commitments};
fn main() -> Result<(), FrostError> {
// Setup: Generate keys for 5 participants with threshold of 3
let threshold = 3;
let total_participants = 5;
let participants = generate_frost_keys(threshold, total_participants)?;
// Get the group public key
let group_public_key = compute_group_public_key(&participants);
// Message to be signed
let message = b"Hello, FROST!";
// Round 1: Generate commitments
let signing_participants = &participants[0..threshold];
let mut commitments = Vec::new();
let mut secret_commitments = Vec::new();
for participant in signing_participants {
let (commitment, secret) = participant.generate_commitment();
commitments.push(commitment);
secret_commitments.push(secret);
}
// Aggregate commitments
let participant_indices: Vec<u32> = signing_participants.iter()
.map(|p| p.index)
.collect();
let group_commitment = aggregate_commitments(
&commitments,
message,
&participant_indices,
group_public_key,
);
// Round 2: Generate signature shares
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
// Aggregate shares into final signature
let signature = aggregate_signatures(
&signature_shares,
group_commitment.aggregated,
message,
group_public_key,
)?;
// Verify the signature
assert!(verify_signature(&signature, message, group_public_key));
Ok(())
}
```

## Features

- Key generation with Shamir's Secret Sharing
- Commitment generation and aggregation
- Signature share generation
- Signature aggregation
- Signature verification
- Binding factors for security
- Lagrange interpolation for threshold signing

## Testing

Run the tests with:

```bash
cargo test
```

## Security Consideration

This implementation is for educational purposes. For production use:
- Audit the code thoroughly
- Add proper error handling
- Implement secure communication between participants
- Consider side-channel attacks
- Add proper secret management

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## References

- [FROST: Flexible Round-Optimized Schnorr Threshold Signatures](https://eprint.iacr.org/2020/852.pdf)
- [curve25519-dalek Documentation](https://docs.rs/curve25519-dalek)