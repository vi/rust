// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use dataflow::move_paths::{HasMoveData, MoveData};
use dataflow::{MaybeObservedLvals, LvalObservers};
use dataflow::{on_all_children_bits, state_for_location};
use dataflow::MoveDataParamEnv;
use dataflow;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;
use rustc::mir::visit::Visitor;
use rustc_data_structures::indexed_set::IdxSetBuf;
use rustc::ty::maps::Providers;
use std::panic::{AssertUnwindSafe, catch_unwind};

// FIXME: This needs to run before optimizations like SimplifyCfg and SimplifyBranches
fn moveck<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId) {
    // NB: this borrow is valid because all the consumers of
    // `mir_const` force this.
    let mir = &*tcx.mir_const(def_id).borrow();
    let id = tcx.hir.as_local_node_id(def_id).unwrap();
    let param_env = tcx.param_env(def_id);
    // FIXME: Make `gather_moves` not panic on MIR errors
    let move_data = catch_unwind(AssertUnwindSafe(|| {
        MoveData::gather_moves(mir, tcx, param_env, true)
    }));
    let move_data = if let Ok(m) = move_data {
        m
    } else {
        // gather_moves panicked, so there will be a borrowck error
        return;
    };
    let env = MoveDataParamEnv {
        move_data: move_data,
        param_env: param_env
    };
    let dead_unwinds = IdxSetBuf::new_empty(mir.basic_blocks().len());
    let analysis = MaybeObservedLvals::new(tcx, mir, &env);
    let observed =
        dataflow::do_dataflow(tcx, mir, id, &[], &dead_unwinds, analysis,
                                |bd, p| &bd.move_data().move_paths[p]);

    for move_out in env.move_data.moves.iter() {
        let state = state_for_location(move_out.source, &analysis, &observed);

        // FIXME: on_all_children_bits - lvalue_contents_drop_state_cannot_differ might
        // not be right here
        on_all_children_bits(tcx, mir, &env.move_data, move_out.path, |child| {
            let lvalue = &env.move_data.move_paths[child].lvalue;
            let lvalue_ty = lvalue.ty(mir, tcx).to_ty(tcx);
            let span = move_out.source.source_info(mir).span;
            if state.contains(&child) && !lvalue_ty.is_move(tcx.global_tcx(), param_env, span) {
                let mut observers = LvalObservers::new(tcx, mir, &env, child);
                observers.visit_mir(mir);

                static STR: &'static &'static str = &"<>";

                let observer_result =
                    dataflow::do_dataflow(tcx, mir, id, &[], &dead_unwinds, observers.clone(),
                                        |_, _| STR);

                let state = state_for_location(move_out.source, &observers, &observer_result);

                let mut err = struct_span_err!(tcx.sess, span, E0901,
                    "cannot move value whose address is observed");

                err.note(&format!("required because `{}` does not implement Move", lvalue_ty));

                for (i, loc) in observers.observers.iter().enumerate() {
                    if state.contains(&i) {
                        span_note!(err,
                                    loc.source_info(mir).span,
                                    "the address was observed here");
                    }
                }

                err.emit();
            }
        });
    }
}

pub(crate) fn provide(providers: &mut Providers) {
    *providers = Providers {
        moveck,
        ..*providers
    };
}
