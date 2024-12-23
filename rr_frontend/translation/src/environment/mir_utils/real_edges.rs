// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rr_rustc_interface::index::IndexVec;
use rr_rustc_interface::middle::mir::{self, TerminatorKind};

/// A data structure to store the non-virtual CFG edges of a MIR body.
pub struct RealEdges {
    successors: IndexVec<mir::BasicBlock, Vec<mir::BasicBlock>>,
    predecessors: IndexVec<mir::BasicBlock, Vec<mir::BasicBlock>>,
}

impl RealEdges {
    pub fn new(body: &mir::Body) -> Self {
        let mut successors: IndexVec<_, Vec<_>> = body.basic_blocks.iter().map(|_| Vec::new()).collect();
        let mut predecessors: IndexVec<_, Vec<_>> = body.basic_blocks.iter().map(|_| Vec::new()).collect();

        for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
            let targets = real_targets(bb_data.terminator());
            for &target in &targets {
                successors[bb].push(target);
                predecessors[target].push(bb);
            }
        }

        Self {
            successors,
            predecessors,
        }
    }

    #[must_use]
    pub fn successors(&self, bb: mir::BasicBlock) -> &[mir::BasicBlock] {
        &self.successors[bb]
    }

    #[must_use]
    pub fn predecessors(&self, bb: mir::BasicBlock) -> &[mir::BasicBlock] {
        &self.predecessors[bb]
    }
}

fn real_targets(terminator: &mir::Terminator) -> Vec<mir::BasicBlock> {
    match &terminator.kind {
        TerminatorKind::Goto { target } | TerminatorKind::Assert { target, .. } => {
            vec![*target]
        },

        TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),

        TerminatorKind::GeneratorDrop
        | TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_) => vec![],

        TerminatorKind::Drop { target, .. } => vec![*target],

        TerminatorKind::Call { target, .. } => match target {
            Some(target) => vec![*target],
            None => vec![],
        },

        TerminatorKind::FalseEdge { real_target, .. } | TerminatorKind::FalseUnwind { real_target, .. } => {
            vec![*real_target]
        },

        TerminatorKind::Yield { resume, .. } => vec![*resume],

        TerminatorKind::InlineAsm { destination, .. } => match destination {
            Some(target) => vec![*target],
            None => vec![],
        },
    }
}
