//! Testing utilities.

#![allow(missing_docs)]

use alloy_primitives::{hex, keccak256, B512};
use anyhow::Result;
use async_trait::async_trait;
use kona_preimage::{HintRouter, PreimageFetcher, PreimageKey, PreimageKeyType};
use std::{collections::HashMap, sync::Arc};
use tokio::sync::Mutex;

/// Used in tests to write the results to
pub const BASE_ADDR_END: u64 = 0xFF_FF_FF_FF_BF_FF_FF_F0;

/// Used as the return-address for tests
pub const END_ADDR: u64 = 0xA7_EF_00_D0;

#[derive(Debug, Default)]
pub struct StaticOracle {
    preimage_data: Vec<u8>,
}

impl StaticOracle {
    pub fn new(preimage_data: Vec<u8>) -> Self {
        Self { preimage_data }
    }
}

#[async_trait]
impl HintRouter for StaticOracle {
    async fn route_hint(&self, _: String) -> Result<()> {
        // no-op
        Ok(())
    }
}

#[async_trait]
impl PreimageFetcher for StaticOracle {
    async fn get_preimage(&self, _: PreimageKey) -> Result<Vec<u8>> {
        Ok(self.preimage_data.clone())
    }
}

#[derive(Debug)]
pub struct ClaimTestOracle {
    images: Arc<Mutex<HashMap<PreimageKey, Vec<u8>>>>,
}

impl ClaimTestOracle {
    pub(crate) const S: u64 = 1000;
    pub(crate) const A: u64 = 3;
    pub(crate) const B: u64 = 4;

    #[inline(always)]
    pub fn diff() -> B512 {
        let mut diff = B512::ZERO;
        diff[..32].copy_from_slice(keccak256(Self::A.to_be_bytes()).as_ref());
        diff[32..].copy_from_slice(keccak256(Self::B.to_be_bytes()).as_ref());
        diff
    }

    #[inline(always)]
    pub fn pre_hash() -> [u8; 32] {
        *keccak256(Self::S.to_be_bytes())
    }

    #[inline(always)]
    pub fn diff_hash() -> [u8; 32] {
        *keccak256(Self::diff().as_slice())
    }
}

impl Default for ClaimTestOracle {
    fn default() -> Self {
        let mut images = HashMap::default();
        images.insert(PreimageKey::new_local(0), Self::pre_hash().to_vec());
        images.insert(PreimageKey::new_local(1), Self::diff_hash().to_vec());
        images.insert(
            PreimageKey::new_local(2),
            (Self::S * Self::A + Self::B).to_be_bytes().to_vec(),
        );

        Self { images: Arc::new(Mutex::new(images)) }
    }
}

#[async_trait]
impl HintRouter for ClaimTestOracle {
    async fn route_hint(&self, s: String) -> Result<()> {
        let parts: Vec<&str> = s.split(' ').collect();

        assert_eq!(parts.len(), 2);

        let part = hex::decode(parts[1]).unwrap();
        assert_eq!(part.len(), 32);
        let hash: [u8; 32] = part.try_into().unwrap();

        match parts[0] {
            "fetch-state" => {
                assert_eq!(hash, Self::pre_hash(), "Expecting request for pre-state preimage");

                self.images.lock().await.insert(
                    PreimageKey::new(Self::pre_hash(), PreimageKeyType::Keccak256),
                    Self::S.to_be_bytes().to_vec(),
                );
            }
            "fetch-diff" => {
                assert_eq!(hash, Self::diff_hash(), "Expecting request for diff preimage");

                let mut images_lock = self.images.lock().await;
                images_lock.insert(
                    PreimageKey::new(Self::diff_hash(), PreimageKeyType::Keccak256),
                    Self::diff().to_vec(),
                );
                images_lock.insert(
                    PreimageKey::new(*keccak256(Self::A.to_be_bytes()), PreimageKeyType::Keccak256),
                    Self::A.to_be_bytes().to_vec(),
                );
                images_lock.insert(
                    PreimageKey::new(*keccak256(Self::B.to_be_bytes()), PreimageKeyType::Keccak256),
                    Self::B.to_be_bytes().to_vec(),
                );
            }
            _ => panic!("Unexpected hint: {}", parts[0]),
        }

        Ok(())
    }
}

#[async_trait]
impl PreimageFetcher for ClaimTestOracle {
    async fn get_preimage(&self, key: PreimageKey) -> Result<Vec<u8>> {
        Ok(self.images.lock().await.get(&key).ok_or(anyhow::anyhow!("No image for key"))?.to_vec())
    }
}
