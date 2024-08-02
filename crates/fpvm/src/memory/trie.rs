//! This module contains the [TrieNode] type, which represents a node within a Radix trie.

use alloy_primitives::{b256, keccak256, Bytes, B256};
use alloy_rlp::{length_of_length, Buf, Decodable, Encodable, Header, EMPTY_STRING_CODE};
use anyhow::{anyhow, Result};
use nybbles::Nibbles;

/// The length of the branch list when RLP encoded
const BRANCH_LIST_LENGTH: usize = 17;

/// The length of a leaf or extension node's RLP encoded list
const LEAF_OR_EXTENSION_LIST_LENGTH: usize = 2;

/// The number of nibbles traversed in a branch node.
const BRANCH_NODE_NIBBLES: usize = 1;

/// Prefix for even-nibbled extension node paths.
const PREFIX_EXTENSION_EVEN: u8 = 0;

/// Prefix for odd-nibbled extension node paths.
const PREFIX_EXTENSION_ODD: u8 = 1;

/// Prefix for even-nibbled leaf node paths.
const PREFIX_LEAF_EVEN: u8 = 2;

/// Prefix for odd-nibbled leaf node paths.
const PREFIX_LEAF_ODD: u8 = 3;

/// Nibble bit width.
const NIBBLE_WIDTH: usize = 4;

/// Root hash of an empty trie.
pub(crate) const EMPTY_ROOT_HASH: B256 =
    b256!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421");

/// A [TrieNode] is a node within a Radix Trie. In this implementation, keys are expected to be
/// fixed-size nibble sequences, and values are arbitrary [Encodable] + [Decodable] types.
///
/// The [TrieNode] has several variants:
/// - [TrieNode::Empty] represents an empty node.
/// - [TrieNode::Leaf] represents a 2-item node with the encoding `rlp([encoded_path, value])`.
/// - [TrieNode::Extension] represents a 2-item pointer node with the encoding `rlp([encoded_path,
///   key])`.
/// - [TrieNode::Branch] represents a node that refers to up to 16 child nodes with the encoding
///   `rlp([ v0, ..., v15, value ])`.
///
/// The [alloy_rlp::Encodable] and [alloy_rlp::Decodable] traits are implemented for [TrieNode],
/// allowing for RLP encoding and decoding of the types for storage and retrieval. The
/// implementation of these traits will not blind the child nodes of the [TrieNode].
///
/// The [Self::root] function will merkle-encode the [TrieNode] recursively and return the hash of
/// the encoded bytes.
///
/// ## SAFETY
/// As this implementation only supports uniform key sizes, the [TrieNode] data structure will fail
/// to behave correctly if confronted with keys of varying lengths. Namely, this is because it does
/// not support the `value` field in branch nodes.
#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub enum TrieNode<V>
where
    V: Clone + Eq + PartialEq + Encodable + Decodable,
{
    /// An empty [TrieNode] is represented as an [EMPTY_STRING_CODE] (0x80).
    #[default]
    Empty,
    /// A leaf node is a 2-item node with the encoding `rlp([encoded_path, value])`
    Leaf {
        /// The key of the leaf node
        prefix: Nibbles,
        /// The value of the leaf node
        value: V,
        /// The cached hash of the leaf node
        /// Invalid if [None]
        cached_hash: Option<B256>,
    },
    /// An extension node is a 2-item pointer node with the encoding `rlp([encoded_path, key])`
    Extension {
        /// The path prefix of the extension
        prefix: Nibbles,
        /// The pointer to the child node
        node: Box<TrieNode<V>>,
        /// The cached hash of the extension node
        /// Invalid if [None]
        cached_hash: Option<B256>,
    },
    /// A branch node refers to up to 16 child nodes with the encoding
    /// `rlp([ v0, ..., v15, value ])`
    Branch {
        /// The 16 child nodes and value of the branch.
        stack: Vec<TrieNode<V>>,
        /// The cached hash of the branch node
        /// Invalid if [None]
        cached_hash: Option<B256>,
    },
}

impl<V> TrieNode<V>
where
    V: Clone + Eq + PartialEq + Encodable + Decodable,
{
    /// Returns the hash of the RLP encoded [TrieNode]. Updates the node's cached hash if it is
    /// currently [None].
    pub fn root(&mut self) -> B256 {
        // Check if the node has a cached hash.
        if let Some(cached_hash) = self.cached_hash() {
            return cached_hash;
        }

        // Encode the node and hash the RLP encoded bytes.
        let mut rlp_buf = Vec::with_capacity(self.merkle_encoding_length());
        self.encode_merkle(&mut rlp_buf);
        let commitment = keccak256(&rlp_buf);

        // Update the node's cached hash.
        match self {
            TrieNode::Empty => (),
            TrieNode::Leaf { cached_hash, .. } |
            TrieNode::Extension { cached_hash, .. } |
            TrieNode::Branch { cached_hash, .. } => *cached_hash = Some(commitment),
        }

        commitment
    }

    /// Returns the cached hash of the [TrieNode], or [None] if it is not cached.
    pub fn cached_hash(&self) -> Option<B256> {
        match self {
            TrieNode::Empty => Some(EMPTY_ROOT_HASH),
            TrieNode::Leaf { cached_hash, .. } |
            TrieNode::Extension { cached_hash, .. } |
            TrieNode::Branch { cached_hash, .. } => *cached_hash,
        }
    }

    /// Returns the number of leaves in the trie rooted at `self`.
    ///
    /// ## Takes
    /// - `self` - The root trie node
    /// - `cache` - The cache of trie nodes
    ///
    /// ## Returns
    /// - `usize` - The number of leaves in the trie
    pub fn leaf_count(&self) -> usize {
        match self {
            TrieNode::Empty => 0,
            TrieNode::Leaf { .. } => 1,
            TrieNode::Extension { node, .. } => node.leaf_count(),
            TrieNode::Branch { stack, .. } => {
                stack.iter().fold(0, |acc, node| acc + node.leaf_count())
            }
        }
    }

    /// Generates a proof for the given K/V pair in the trie rooted at `self`.
    ///
    /// ## Takes
    /// - `path` - The nibbles representation of the path to the leaf node
    ///
    /// ## Returns
    /// - `Ok(Vec<Bytes>)` - The proof for the given K/V pair
    /// - `Err(_)` - Proof generation error
    pub fn proof(&mut self, path: &Nibbles) -> Result<Vec<Bytes>> {
        let mut proof = Vec::with_capacity(8);

        match self {
            TrieNode::Branch { stack, .. } => {
                let branch_nibble = path[0] as usize;
                if let Some(node) = stack.get_mut(branch_nibble) {
                    // Continue proof generation recursively
                    proof.extend(node.proof(&path.slice(BRANCH_NODE_NIBBLES..))?);

                    // Encode the branch node
                    let mut rlp_buf = Vec::with_capacity(self.merkle_encoding_length());
                    self.encode_merkle(&mut rlp_buf);
                    proof.push(rlp_buf.into());
                } else {
                    anyhow::bail!("Key does not exist in trie (branch node mismatch)")
                }
            }
            TrieNode::Leaf { prefix, .. } => {
                if path == prefix {
                    let mut rlp_buf = Vec::with_capacity(self.merkle_encoding_length());
                    self.encode_merkle(&mut rlp_buf);
                    proof.push(rlp_buf.into());
                } else {
                    anyhow::bail!("Key does not exist in trie (leaf node mismatch)")
                }
            }
            TrieNode::Extension { prefix, node, .. } => {
                if path.slice(..prefix.len()).as_slice() == prefix.as_slice() {
                    // Continue proof generation recursively
                    proof.extend(node.proof(&path.slice(prefix.len()..))?);

                    // Encode the extension node
                    let mut rlp_buf = Vec::with_capacity(self.merkle_encoding_length());
                    self.encode_merkle(&mut rlp_buf);
                    proof.push(rlp_buf.into());
                } else {
                    anyhow::bail!("Key does not exist in trie (extension node mismatch)")
                }
            }
            TrieNode::Empty => {
                anyhow::bail!("Key does not exist in trie (empty node)")
            }
        }

        Ok(proof)
    }

    /// Walks down the trie to a leaf value with the given key, if it exists. Preimages for blinded
    /// nodes along the path are fetched using the `fetcher` function, and persisted in the inner
    /// [TrieNode] elements.
    ///
    /// ## Takes
    /// - `self` - The root trie node
    /// - `path` - The nibbles representation of the path to the leaf node
    /// - `fetcher` - The preimage fetcher for intermediate blinded nodes
    ///
    /// ## Returns
    /// - `Err(_)` - Could not retrieve the node with the given key from the trie.
    /// - `Ok((_, _))` - The key and value of the node
    pub fn open<'a>(&'a mut self, path: &Nibbles, invalidate: bool) -> Result<Option<&'a mut V>> {
        match self {
            TrieNode::Branch { ref mut stack, cached_hash } => {
                if invalidate {
                    *cached_hash = None;
                }

                let branch_nibble = path[0] as usize;
                stack
                    .get_mut(branch_nibble)
                    .map(|node| node.open(&path.slice(BRANCH_NODE_NIBBLES..), invalidate))
                    .unwrap_or(Ok(None))
            }
            TrieNode::Leaf { prefix, value, cached_hash } => {
                if invalidate {
                    *cached_hash = None;
                }
                Ok((path.as_slice() == prefix.as_slice()).then_some(value))
            }
            TrieNode::Extension { prefix, node, cached_hash } => {
                if path.slice(..prefix.len()).as_slice() == prefix.as_slice() {
                    if invalidate {
                        *cached_hash = None;
                    }

                    // Follow extension branch
                    node.open(&path.slice(prefix.len()..), invalidate)
                } else {
                    Ok(None)
                }
            }
            TrieNode::Empty => Ok(None),
        }
    }

    /// Inserts a [TrieNode] at the given path into the trie rooted at Self.
    ///
    /// ## Takes
    /// - `self` - The root trie node
    /// - `path` - The nibbles representation of the path to the leaf node
    /// - `node` - The node to insert at the given path
    /// - `fetcher` - The preimage fetcher for intermediate blinded nodes
    ///
    /// ## Returns
    /// - `Err(_)` - Could not insert the node at the given path in the trie.
    /// - `Ok(())` - The node was successfully inserted at the given path.
    pub fn insert(&mut self, path: &Nibbles, value: V) -> Result<()> {
        match self {
            TrieNode::Empty => {
                // If the trie node is null, insert the leaf node at the current path.
                *self = TrieNode::Leaf { prefix: path.clone(), value, cached_hash: None };
                Ok(())
            }
            TrieNode::Leaf { prefix, value: leaf_value, .. } => {
                let shared_extension_nibbles = path.common_prefix_length(prefix);

                // If all nibbles are shared, update the leaf node with the new value.
                if path.as_slice() == prefix.as_slice() {
                    *self = TrieNode::Leaf { prefix: prefix.clone(), value, cached_hash: None };
                    return Ok(());
                }

                // Create a branch node stack containing the leaf node and the new value.
                let mut stack = vec![TrieNode::Empty; BRANCH_LIST_LENGTH];

                // Insert the shortened extension into the branch stack.
                let extension_nibble = prefix[shared_extension_nibbles] as usize;
                stack[extension_nibble] = TrieNode::Leaf {
                    prefix: prefix.slice(shared_extension_nibbles + BRANCH_NODE_NIBBLES..),
                    value: leaf_value.clone(),
                    cached_hash: None,
                };

                // Insert the new value into the branch stack.
                let branch_nibble_new = path[shared_extension_nibbles] as usize;
                stack[branch_nibble_new] = TrieNode::Leaf {
                    prefix: path.slice(shared_extension_nibbles + BRANCH_NODE_NIBBLES..),
                    value,
                    cached_hash: None,
                };

                // Replace the leaf node with the branch if no nibbles are shared, else create an
                // extension.
                if shared_extension_nibbles == 0 {
                    *self = TrieNode::Branch { stack, cached_hash: None };
                } else {
                    let raw_ext_nibbles = path.slice(..shared_extension_nibbles);
                    *self = TrieNode::Extension {
                        prefix: raw_ext_nibbles,
                        node: Box::new(TrieNode::Branch { stack, cached_hash: None }),
                        cached_hash: None,
                    };
                }
                Ok(())
            }
            TrieNode::Extension { prefix, node, cached_hash } => {
                let shared_extension_nibbles = path.common_prefix_length(prefix);
                if shared_extension_nibbles == prefix.len() {
                    // Invalidate the extension node's cached hash.
                    *cached_hash = None;

                    node.insert(&path.slice(shared_extension_nibbles..), value)?;
                    return Ok(());
                }

                // Create a branch node stack containing the leaf node and the new value.
                let mut stack = vec![TrieNode::Empty; BRANCH_LIST_LENGTH];

                // Insert the shortened extension into the branch stack.
                let extension_nibble = prefix[shared_extension_nibbles] as usize;
                let new_prefix = prefix.slice(shared_extension_nibbles + BRANCH_NODE_NIBBLES..);
                stack[extension_nibble] = if new_prefix.is_empty() {
                    // In the case that the extension node no longer has a prefix, insert the node
                    // verbatim into the branch.
                    node.as_ref().clone()
                } else {
                    TrieNode::Extension {
                        prefix: new_prefix,
                        node: node.clone(),
                        cached_hash: None,
                    }
                };

                // Insert the new value into the branch stack.
                let branch_nibble_new = path[shared_extension_nibbles] as usize;
                stack[branch_nibble_new] = TrieNode::Leaf {
                    prefix: path.slice(shared_extension_nibbles + BRANCH_NODE_NIBBLES..),
                    value,
                    cached_hash: None,
                };

                // Replace the extension node with the branch if no nibbles are shared, else create
                // an extension.
                if shared_extension_nibbles == 0 {
                    *self = TrieNode::Branch { stack, cached_hash: None };
                } else {
                    let extension = path.slice(..shared_extension_nibbles);
                    *self = TrieNode::Extension {
                        prefix: extension,
                        node: Box::new(TrieNode::Branch { stack, cached_hash: None }),
                        cached_hash: None,
                    };
                }
                Ok(())
            }
            TrieNode::Branch { stack, cached_hash } => {
                // Invalidate the branch node's cached hash.
                *cached_hash = None;

                // Follow the branch node to the next node in the path.
                let branch_nibble = path[0] as usize;
                stack[branch_nibble].insert(&path.slice(BRANCH_NODE_NIBBLES..), value)
            }
        }
    }

    /// Returns the RLP payload length of the [TrieNode], when encoding for full snapshots.
    pub(crate) fn payload_length(&self) -> usize {
        match self {
            TrieNode::Empty => 0,
            TrieNode::Leaf { prefix, value, .. } => {
                let mut encoded_key_len = prefix.len() / 2 + 1;
                if encoded_key_len != 1 {
                    encoded_key_len += length_of_length(encoded_key_len);
                }
                encoded_key_len + value.length()
            }
            TrieNode::Extension { prefix, node, .. } => {
                let mut encoded_key_len = prefix.len() / 2 + 1;
                if encoded_key_len != 1 {
                    encoded_key_len += length_of_length(encoded_key_len);
                }
                encoded_key_len + node.length()
            }
            TrieNode::Branch { stack, .. } => stack.iter().fold(0, |mut acc, node| {
                acc += node.length();
                acc
            }),
        }
    }

    /// Encodes the [TrieNode] with child nodes hashed.
    ///
    /// This function is semantically very different from [Encodable::encode], in that it will blind
    /// the children of the [TrieNode].
    pub(crate) fn encode_merkle(&mut self, out: &mut dyn alloy_rlp::BufMut) {
        let payload_length = self.merkle_payload_length();
        match self {
            Self::Empty => out.put_u8(EMPTY_STRING_CODE),
            Self::Leaf { prefix, value, .. } => {
                // Encode the leaf node's header and key-value pair.
                Header { list: true, payload_length }.encode(out);
                prefix.encode_path_leaf(true).as_slice().encode(out);
                value.encode(out);
            }
            Self::Extension { prefix, node, .. } => {
                // Encode the extension node's header, prefix, and pointer node.
                Header { list: true, payload_length }.encode(out);
                prefix.encode_path_leaf(false).as_slice().encode(out);
                node.root().encode(out);
            }
            Self::Branch { stack, .. } => {
                // In branch nodes, if an element is longer than 32 bytes in length, it is blinded.
                // Assuming we have an open trie node, we must re-hash the elements
                // that are longer than 32 bytes in length.
                Header { list: true, payload_length }.encode(out);
                stack.iter_mut().for_each(|node| {
                    if matches!(node, TrieNode::Empty) {
                        out.put_u8(EMPTY_STRING_CODE)
                    } else {
                        node.root().encode(out)
                    };
                });
            }
        }
    }

    /// Returns the length of [TrieNode] when RLP encoded for merkleization.
    pub(crate) fn merkle_encoding_length(&self) -> usize {
        match self {
            Self::Empty => 1,
            Self::Leaf { .. } => {
                let payload_length = self.merkle_payload_length();
                Header { list: true, payload_length }.length() + payload_length
            }
            Self::Extension { .. } => {
                let payload_length = self.merkle_payload_length();
                Header { list: true, payload_length }.length() + payload_length
            }
            Self::Branch { .. } => {
                let payload_length = self.merkle_payload_length();
                Header { list: true, payload_length }.length() + payload_length
            }
        }
    }

    /// Returns the RLP payload length of the [TrieNode], when encoding for merkleization.
    pub(crate) fn merkle_payload_length(&self) -> usize {
        match self {
            TrieNode::Empty => 0,
            TrieNode::Leaf { prefix, value, .. } => {
                let mut encoded_key_len = prefix.len() / 2 + 1;
                if encoded_key_len != 1 {
                    encoded_key_len += length_of_length(encoded_key_len);
                }
                encoded_key_len + value.length()
            }
            TrieNode::Extension { prefix, .. } => {
                let mut encoded_key_len = prefix.len() / 2 + 1;
                if encoded_key_len != 1 {
                    encoded_key_len += length_of_length(encoded_key_len);
                }
                encoded_key_len + B256::ZERO.length()
            }
            TrieNode::Branch { stack, .. } => stack.iter().fold(0, |mut acc, node| {
                acc += if matches!(node, TrieNode::Empty) { 1 } else { B256::ZERO.length() };
                acc
            }),
        }
    }

    /// Attempts to convert a `path` and `value` into a [TrieNode], if they correspond to a
    /// [TrieNode::Leaf] or [TrieNode::Extension].
    ///
    /// **Note:** This function assumes that the passed reader has already consumed the RLP header
    /// of the [TrieNode::Leaf] or [TrieNode::Extension] node.
    fn try_decode_leaf_or_extension_payload(buf: &mut &[u8]) -> Result<Self> {
        // Decode the path and value of the leaf or extension node.
        let path = Bytes::decode(buf).map_err(|e| anyhow!("Failed to decode: {e}"))?;
        let first_nibble = path[0] >> NIBBLE_WIDTH;
        let first = match first_nibble {
            PREFIX_EXTENSION_ODD | PREFIX_LEAF_ODD => Some(path[0] & 0x0F),
            PREFIX_EXTENSION_EVEN | PREFIX_LEAF_EVEN => None,
            _ => anyhow::bail!("Unexpected path identifier in high-order nibble"),
        };

        // Check the high-order nibble of the path to determine the type of node.
        match first_nibble {
            PREFIX_EXTENSION_EVEN | PREFIX_EXTENSION_ODD => {
                // Extension node
                let extension_node_value =
                    TrieNode::decode(buf).map_err(|e| anyhow!("Failed to decode: {e}"))?;
                Ok(TrieNode::Extension {
                    prefix: unpack_path_to_nibbles(first, path[1..].as_ref()),
                    node: Box::new(extension_node_value),
                    cached_hash: None,
                })
            }
            PREFIX_LEAF_EVEN | PREFIX_LEAF_ODD => {
                // Leaf node
                let value = V::decode(buf).map_err(|e| anyhow!("Failed to decode: {e}"))?;
                Ok(TrieNode::Leaf {
                    prefix: unpack_path_to_nibbles(first, path[1..].as_ref()),
                    value,
                    cached_hash: None,
                })
            }
            _ => {
                anyhow::bail!("Unexpected path identifier in high-order nibble")
            }
        }
    }
}

impl<V> Encodable for TrieNode<V>
where
    V: Clone + Eq + PartialEq + Encodable + Decodable,
{
    fn encode(&self, out: &mut dyn alloy_rlp::BufMut) {
        match self {
            Self::Empty => out.put_u8(EMPTY_STRING_CODE),
            Self::Leaf { prefix, value, .. } => {
                // Encode the leaf node's header and key-value pair.
                Header { list: true, payload_length: self.payload_length() }.encode(out);
                prefix.encode_path_leaf(true).as_slice().encode(out);
                value.encode(out);
            }
            Self::Extension { prefix, node, .. } => {
                // Encode the extension node's header, prefix, and pointer node.
                Header { list: true, payload_length: self.payload_length() }.encode(out);
                prefix.encode_path_leaf(false).as_slice().encode(out);
                node.encode(out);
            }
            Self::Branch { stack, .. } => {
                // In branch nodes, if an element is longer than 32 bytes in length, it is blinded.
                // Assuming we have an open trie node, we must re-hash the elements
                // that are longer than 32 bytes in length.
                Header { list: true, payload_length: self.payload_length() }.encode(out);
                stack.iter().for_each(|node| {
                    node.encode(out);
                });
            }
        }
    }

    fn length(&self) -> usize {
        match self {
            Self::Empty => 1,
            Self::Leaf { .. } => {
                let payload_length = self.payload_length();
                Header { list: true, payload_length }.length() + payload_length
            }
            Self::Extension { .. } => {
                let payload_length = self.payload_length();
                Header { list: true, payload_length }.length() + payload_length
            }
            Self::Branch { .. } => {
                let payload_length = self.payload_length();
                Header { list: true, payload_length }.length() + payload_length
            }
        }
    }
}

impl<V> Decodable for TrieNode<V>
where
    V: Clone + Eq + PartialEq + Encodable + Decodable,
{
    /// Attempts to decode the [TrieNode].
    fn decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
        // Peek at the header to determine the type of Trie node we're currently decoding.
        let header = Header::decode(&mut (**buf).as_ref())?;

        if header.list {
            // Peek at the RLP stream to determine the number of elements in the list.
            let list_length = rlp_list_element_length(&mut (**buf).as_ref())?;

            match list_length {
                BRANCH_LIST_LENGTH => {
                    let list = Vec::<TrieNode<V>>::decode(buf)?;
                    Ok(Self::Branch { stack: list, cached_hash: None })
                }
                LEAF_OR_EXTENSION_LIST_LENGTH => {
                    // Advance the buffer to the start of the list payload.
                    buf.advance(header.length());
                    // Decode the leaf or extension node's raw payload.
                    Self::try_decode_leaf_or_extension_payload(buf)
                        .map_err(|_| alloy_rlp::Error::UnexpectedList)
                }
                _ => Err(alloy_rlp::Error::UnexpectedLength),
            }
        } else {
            match header.payload_length {
                0 => {
                    buf.advance(header.length());
                    Ok(Self::Empty)
                }
                _ => Err(alloy_rlp::Error::UnexpectedLength),
            }
        }
    }
}

/// Walks through a RLP list's elements and returns the total number of elements in the list.
/// Returns [alloy_rlp::Error::UnexpectedString] if the RLP stream is not a list.
///
/// ## Takes
/// - `buf` - The RLP stream to walk through
///
/// ## Returns
/// - `Ok(usize)` - The total number of elements in the list
/// - `Err(_)` - The RLP stream is not a list
fn rlp_list_element_length(buf: &mut &[u8]) -> alloy_rlp::Result<usize> {
    let header = Header::decode(buf)?;
    if !header.list {
        return Err(alloy_rlp::Error::UnexpectedString);
    }
    let len_after_consume = buf.len() - header.payload_length;

    let mut list_element_length = 0;
    while buf.len() > len_after_consume {
        let header = Header::decode(buf)?;
        buf.advance(header.payload_length);
        list_element_length += 1;
    }
    Ok(list_element_length)
}

/// Unpack node path to nibbles.
///
/// ## Takes
/// - `first` - first nibble of the path if it is odd. Must be <= 0x0F, or will create invalid
///   nibbles.
/// - `rest` - rest of the nibbles packed
///
/// ## Returns
/// - `Nibbles` - unpacked nibbles
fn unpack_path_to_nibbles(first: Option<u8>, rest: &[u8]) -> Nibbles {
    let rest = Nibbles::unpack(rest);
    Nibbles::from_vec_unchecked(first.into_iter().chain(rest.iter().copied()).collect::<Vec<u8>>())
}
