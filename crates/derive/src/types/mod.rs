//! This module contains all of the types used within the derivation pipeline.

// Re-export the kona primitives.
pub use kona_primitives::*;

// Re-export alloy consensus primitives.
pub use alloy_consensus::{Header, Receipt, TxEnvelope};

pub mod batch;
pub use batch::{
    Batch, BatchType, BatchValidity, BatchWithInclusionBlock, RawSpanBatch, SingleBatch, SpanBatch,
    SpanBatchBits, SpanBatchEip1559TransactionData, SpanBatchEip2930TransactionData,
    SpanBatchElement, SpanBatchError, SpanBatchLegacyTransactionData, SpanBatchPayload,
    SpanBatchPrefix, SpanBatchTransactionData, SpanBatchTransactions, SpanDecodingError,
    MAX_SPAN_BATCH_SIZE,
};

/// Re-export eip4844 primitives.
pub use alloy_eips::eip4844::{Blob, BYTES_PER_BLOB, VERSIONED_HASH_VERSION_KZG};

mod ecotone;
pub use ecotone::*;

mod blob;
pub use blob::{BlobData, BlobDecodingError, IndexedBlobHash};

mod sidecar;
pub use sidecar::{
    APIBlobSidecar, APIConfigResponse, APIGenesisResponse, APIGetBlobSidecarsResponse,
    APIVersionResponse, BeaconBlockHeader, BlobSidecar, SignedBeaconBlockHeader,
    VersionInformation, KZG_COMMITMENT_SIZE, KZG_PROOF_SIZE,
};

mod frame;
pub use frame::Frame;

mod channel;
pub use channel::Channel;

mod errors;
pub use errors::*;
