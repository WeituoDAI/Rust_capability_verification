// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rr_rustc_interface::middle::{mir, ty};

use crate::environment::mir_utils::tuple_items_for_ty::TupleItemsForTy;

pub trait SplitAggregateAssignment<'tcx> {
    /// Transforms an assignment into its atomic parts. For a normal assignment like
    /// ```ignore
    ///     _3 = move _2;
    /// ```
    /// this is simply returning the assignment itself. But for an aggregate assignment like
    /// ```ignore
    ///     _3 = (move _1, move _2);
    /// ```
    /// there is one atomic assignment for every tuple field. In this example, the atomic
    /// assignments would be
    /// ```ignore
    ///     _3.0 = move _1;
    ///     _3.1 = move _2;
    /// ```
    ///
    /// Statements that are no assignments are returned untouched.
    fn split_assignment(self, tcx: ty::TyCtxt<'tcx>, mir: &mir::Body<'tcx>) -> Vec<mir::Statement<'tcx>>;
}

impl<'tcx> SplitAggregateAssignment<'tcx> for mir::Statement<'tcx> {
    fn split_assignment(self, tcx: ty::TyCtxt<'tcx>, mir: &mir::Body<'tcx>) -> Vec<mir::Statement<'tcx>> {
        let mir::StatementKind::Assign(box (lhs, rhs)) = self.kind else {
            return vec![self];
        };

        let atomic_assignments = match rhs {
            mir::Rvalue::Aggregate(box kind, operands) => {
                // TODO: we should also support structs.
                assert_eq!(kind, mir::AggregateKind::Tuple, "The only supported aggregates are tuples.");
                let local = lhs.as_local().unwrap();
                let items_ty = mir.local_decls[local].ty.tuple_items().unwrap();
                operands
                    .into_iter()
                    .zip(items_ty)
                    .enumerate()
                    .map(|(i, (rhs, ty))| {
                        let lhs = tcx.mk_place_field(local.into(), i.into(), ty);
                        let rhs = mir::Rvalue::Use(rhs);
                        (lhs, rhs)
                    })
                    .collect()
            },
            mir::Rvalue::Use(_) | mir::Rvalue::Ref(_, _, _) => vec![(lhs, rhs)],
            // slice creation is ok
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize),
                _,
                ty,
            ) if ty.is_slice() && !ty.is_unsafe_ptr() => vec![(lhs, rhs)],
            _ => unreachable!("Rvalue {:?} is not supported", rhs),
        };

        let source_info = self.source_info;
        atomic_assignments
            .into_iter()
            .map(|(lhs, rhs)| {
                let kind = mir::StatementKind::Assign(Box::new((lhs, rhs)));
                mir::Statement { source_info, kind }
            })
            .collect()
    }
}
