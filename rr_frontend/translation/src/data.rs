// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines data structures exchanged between a verifier and
//! its environment.

use rr_rustc_interface::hir::def_id::DefId;

/// A unique identifier of the Rust procedure.
pub type ProcedureDefId = DefId;

/// A list of items to verify that is passed to a verifier.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct VerificationTask {
    /// A list of procedures to verify.
    pub procedures: Vec<DefId>,
}

/// Verification result returned by a verifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum VerificationResult {
    /// Verification was successful.
    Success,
    /// Verification failed. Errors should have been already emitted by
    /// the verifier.
    Failure,
}
