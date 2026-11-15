// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kernel-checked, value-polymorphic laws for effectful evaluation.
//!
//! `Run State Error Value = State -> Prod State (Except Error Value)` retains
//! the current state even on failure. Sequencing never invokes a continuation
//! after failure; branching invokes only the selected computation. Thunks retain
//! a lexical environment, not a state snapshot or a memoized result.
//!
//! This is a mathematical vocabulary, not executable IR or translation
//! authority. Its theorems say nothing about a program until an endpoint-aware
//! checker reconstructs that program's semantics and checks the corresponding
//! theorem application. In particular, no library theorem name authorizes a
//! `Certified` obligation, Core admission, runtime provider, or native image.
//!
//! ## Exact public telescopes
//!
//! All arguments below are explicit; every constant has universe argument `u`.
//! Types `S, E, A, B, D, C, L : Type u` are state, error, values, dynamic context,
//! and lexical environment respectively. `Obs A` abbreviates `Prod S (Except E A)`.
//! The congruence law permits different lexical types `Ls, Lt : Type u`.
//!
//! ```text
//! Run S E A                   := S -> Obs A
//! pure S E A a s              = (s, ok a)
//! fail S E A error s          = (s, error error)
//! bind S E A B m k s          = match m s with
//!                                | (s', error e) => (s', error e)
//!                                | (s', ok a)    => k a s'
//! branch S E A flag yes no s  = if flag then yes s else no s
//! Thunk S E A C L             := Prod L (L -> C -> Run S E A)
//! capture S E A C L code lex  := (lex, code)
//! force S E A C L thunk ctx s := thunk.snd thunk.fst ctx s
//! Cps S E A R                 := S -> (S -> A -> R) -> (S -> E -> R) -> R
//! toCps S E A R m s ok err    = match m s with
//!                                | (s', error e) => err s' e
//!                                | (s', ok a)    => ok s' a
//! fromCps S E A f s           = f s (fun s' a => (s', ok a))
//!                                   (fun s' e => (s', error e))
//!
//! bind_congr S E A B m n k l
//!   (hm : forall s, m s = n s)
//!   (hk : forall a s, k a s = l a s) s : bind m k s = bind n l s
//! bind_assoc S E A B D m k h s :
//!   bind (bind m k) h s = bind m (fun a => bind (k a) h) s
//! branch_congr S E A flag yes yes' no no'
//!   (hy : forall s, yes s = yes' s)
//!   (hn : forall s, no s = no' s) s :
//!   branch flag yes no s = branch flag yes' no' s
//! force_capture S E A C L code lex ctx s :
//!   force (capture code lex) ctx s = code lex ctx s
//! force_congr S E A C Ls Lt source target sourceLex targetLex
//!   (h : forall ctx s, source sourceLex ctx s = target targetLex ctx s) ctx s :
//!   force S E A C Ls (capture S E A C Ls source sourceLex) ctx s =
//!   force S E A C Lt (capture S E A C Lt target targetLex) ctx s
//! from_to_cps S E A m s :
//!   fromCps S E A (toCps S E A (Prod S (Except E A)) m) s = m s
//! to_cps_bind S E A B R m k s ok err :
//!   toCps S E B R (bind S E A B m k) s ok err =
//!   toCps S E A R m s (fun s' a => toCps S E B R (k a) s' ok err) err
//! to_cps_branch S E A R flag yes no s ok err :
//!   toCps S E A R (branch S E A flag yes no) s ok err =
//!   if flag then toCps S E A R yes s ok err else toCps S E A R no s ok err
//! to_cps_force_capture S E A C L R code lex ctx s ok err :
//!   toCps S E A R (force S E A C L (capture S E A C L code lex) ctx) s ok err =
//!   toCps S E A R (code lex ctx) s ok err
//! ```
//!
//! The branch condition can itself be an effectful computation: sequence it
//! using `bind` before `branch`. There is deliberately no eager-argument,
//! call-by-need, effect-commutation, or recursion/fixpoint theorem here.
//! Force congruence requires a proof about the distinct captured computations;
//! it does not assume equal callback identities, lexical representations, or
//! recursive bodies. Equality includes the updated state and the entire error
//! or success payload, at every current context/state supplied by a caller.
//! The CPS bridge permits any answer type `R : Type u`. Only the Run-to-CPS-to-Run
//! roundtrip is asserted: an arbitrary fixed-answer CPS term may discard or
//! duplicate its continuations and need not belong to the image of `toCps`.

use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Expr, Level, Name, TypeChecker};

#[path = "semantic_evaluation_case_map.rs"]
mod case_map;
pub use case_map::{
    CASE_MAP_BOOL, CASE_MAP_EXCEPT, CASE_MAP_OPTION, CASE_MAP_PROD, CASE_MAP_THEOREMS,
    LIST_PROJECTION, install_case_maps_into, install_list_projection_into,
};

#[path = "semantic_evaluation_guarded_cleanup.rs"]
mod guarded_cleanup;
pub use guarded_cleanup::{
    GUARDED_CLEANUP_DECODE_FIRST, GUARDED_CLEANUP_RAW_FIRST, GUARDED_RAW_CLEANUP,
    install_guarded_raw_cleanup_into,
};

#[path = "semantic_evaluation_normal_post.rs"]
mod normal_post;
pub use normal_post::{
    NORMAL_OBSERVATION, NORMAL_OBSERVATION_POST, NORMAL_POST, install_normal_post_into,
};

#[path = "semantic_evaluation_normal_value_post.rs"]
mod normal_value_post;
pub use normal_value_post::{
    NORMAL_VALUE_OBSERVATION, NORMAL_VALUE_OBSERVATION_POST, install_normal_value_post_into,
};

#[path = "semantic_evaluation_frame.rs"]
mod framing;
pub use framing::{CPS_IMAGE_FROM, install_image_observation_into};
pub use framing::{
    FRAME_BIND, FRAME_DECLARATIONS, FRAME_EXPOSE, FRAME_FORCE_CAPTURE, FRAME_OBSERVATION,
    FRAME_PRESERVES, FRAME_RUN, install_framing_into,
};

#[path = "semantic_evaluation_success_frame.rs"]
mod success_framing;
pub use success_framing::{
    SUCCESS_FRAME_BASE, SUCCESS_FRAME_BIND, SUCCESS_FRAME_BIND_CONSTANT_OBSERVER,
    SUCCESS_FRAME_BIND_PRESERVES, SUCCESS_FRAME_CPS_OBSERVER, SUCCESS_FRAME_DECLARATIONS,
    SUCCESS_FRAME_ERROR, SUCCESS_FRAME_EXPOSE, SUCCESS_FRAME_OBSERVATION, SUCCESS_FRAME_PRESERVES,
    SUCCESS_FRAME_PROJECTION, SUCCESS_FRAME_RUN, install_success_framing_into,
};

#[path = "semantic_evaluation_success_frame_handle.rs"]
mod success_handle_observer;
pub use success_handle_observer::{
    SUCCESS_FRAME_HANDLE_CONSTANT_OBSERVER, install_success_handle_observer_into,
};

#[path = "semantic_evaluation_success_frame_handle_related.rs"]
mod success_handle_related;
pub use success_handle_related::{
    SUCCESS_FRAME_HANDLE_RELATED_OBSERVER, install_success_handle_related_into,
};

#[path = "semantic_evaluation_success_frame_cps.rs"]
mod success_cps_rule;
pub use success_cps_rule::{SUCCESS_FRAME_CPS_RULE, install_success_cps_rule_into};

#[path = "semantic_evaluation_cps_constant.rs"]
mod cps_constant_observer;
pub use cps_constant_observer::{
    CPS_IMAGE_CONSTANT_OBSERVER, install_image_constant_observer_into,
};

#[path = "semantic_evaluation_cps_callback.rs"]
mod cps_callback;
pub use cps_callback::{CPS_IMAGE_CALLBACK_CONGR, install_image_callback_congruence_into};

#[path = "semantic_evaluation_handle.rs"]
mod handling;
pub use handling::{CPS_IMAGE, CPS_IMAGE_HANDLE, HANDLE, TO_CPS_HANDLE, install_handle_into};

#[path = "semantic_evaluation_loop.rs"]
mod loops;
pub use loops::{
    DOMAIN_AT, DOMAIN_AT_COVER, DOMAIN_AT_END, DOMAIN_AT_MEMBERS, DOMAIN_AT_SOUND,
    install_indexed_domain_into,
};
pub use loops::{DOMAIN_COMPLETE, DOMAIN_FOLD, DOMAIN_LENGTH, DOMAIN_STEP, install_domain_into};
pub use loops::{
    DOMAIN_ENUMERATE, DOMAIN_ENUMERATE_AT, DOMAIN_ENUMERATE_END, DOMAIN_ENUMERATE_LENGTH,
    DOMAIN_ENUMERATE_NONE, DOMAIN_ENUMERATE_SOME, install_enumerated_domain_into,
};
pub use loops::{LOOP_COMPLETE_TRANSFER, LOOP_PREFIX, LOOP_PREFIX_CONGR, install_loop_into};
pub use loops::{LOOP_CPS_COMPLETE_TRANSFER, install_cps_completion_into};
pub use loops::{
    LOOP_CPS_PREFIX, LOOP_CPS_PREFIX_CONGR, LOOP_CPS_PREFIX_FROM_PULSE, install_cps_loop_into,
};
pub use loops::{LOOP_CPS_PREFIX_OBSERVATION, install_cps_observation_into};
pub use loops::{LOOP_RANK_COMPLETE, install_ranked_loop_into};

pub use loops::{
    DOMAIN_TAIL_COMPLETE, DOMAIN_TAIL_FOLD, DOMAIN_TAIL_STEP, install_tail_domain_into,
};
pub use loops::{IMAGE_TO_PULSE, RUN_TO_PULSE, RUN_TO_PULSE_CPS, install_cut_run_into};
pub use loops::{LOOP_MAP_COMPLETE, LOOP_MAP_PREFIX, LOOP_MAP_PULSE, install_loop_map_into};

pub const RUN: &str = "TrustIR.Eval.Run";
pub const PURE: &str = "TrustIR.Eval.pure";
pub const FAIL: &str = "TrustIR.Eval.fail";
pub const BIND: &str = "TrustIR.Eval.bind";
pub const BRANCH: &str = "TrustIR.Eval.branch";
pub const THUNK: &str = "TrustIR.Eval.Thunk";
pub const CAPTURE: &str = "TrustIR.Eval.capture";
pub const FORCE: &str = "TrustIR.Eval.force";
pub const BIND_CONGR: &str = "TrustIR.Eval.bind_congr";
pub const BIND_ASSOC: &str = "TrustIR.Eval.bind_assoc";
pub const BRANCH_CONGR: &str = "TrustIR.Eval.branch_congr";
pub const FORCE_CAPTURE: &str = "TrustIR.Eval.force_capture";
pub const FORCE_CONGR: &str = "TrustIR.Eval.force_congr";
pub const CPS: &str = "TrustIR.Eval.Cps";
pub const TO_CPS: &str = "TrustIR.Eval.toCps";
pub const FROM_CPS: &str = "TrustIR.Eval.fromCps";
pub const FROM_TO_CPS: &str = "TrustIR.Eval.from_to_cps";
pub const TO_CPS_BIND: &str = "TrustIR.Eval.to_cps_bind";
pub const TO_CPS_BRANCH: &str = "TrustIR.Eval.to_cps_branch";
pub const TO_CPS_FORCE_CAPTURE: &str = "TrustIR.Eval.to_cps_force_capture";

// Together with THEOREMS, this is the complete owned-name inventory. Keep the
// preflight independent of installation order: even a collision at the last
// theorem must reject before initializing any prerequisite declarations.
const DEFINITIONS: &[&str] = &[
    RUN, PURE, FAIL, BIND, BRANCH, THUNK, CAPTURE, FORCE, CPS, TO_CPS, FROM_CPS,
];

/// Every declaration uses one universe parameter `u`; its type parameters are
/// arbitrary `Type u`, not numeric carriers. Each theorem is pointwise (no
/// function-extensionality axiom).
pub const THEOREMS: &[&str] = &[
    BIND_CONGR,
    BIND_ASSOC,
    BRANCH_CONGR,
    FORCE_CAPTURE,
    FORCE_CONGR,
    FROM_TO_CPS,
    TO_CPS_BIND,
    TO_CPS_BRANCH,
    TO_CPS_FORCE_CAPTURE,
];

/// Default per-declaration/checker reduction budget. Exhaustion is rejection.
pub const HEARTBEAT_LIMIT: u32 = 1_000_000;
pub const CACHE_ENTRY_LIMIT: usize = 16_384;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticEvaluationError {
    pub declaration: String,
    pub reason: String,
}

impl std::fmt::Display for SemanticEvaluationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.declaration, self.reason)
    }
}

impl std::error::Error for SemanticEvaluationError {}

fn error(name: &str, reason: impl std::fmt::Debug) -> SemanticEvaluationError {
    SemanticEvaluationError {
        declaration: name.into(),
        reason: format!("{reason:?}"),
    }
}

/// Construct a fresh vocabulary and independently recheck its actual theorem
/// terms and rooted authority closures. No non-foundational axioms are allowed
/// in a theorem's closure. No independent micro-check verdict is claimed.
///
/// `Except`'s initializer also installs unrelated transformer stubs. No law
/// references those declarations: the rooted audit is intentionally about
/// actual dependencies, not whether an environment contains an unused axiom.
pub fn build_environment() -> Result<Environment, SemanticEvaluationError> {
    let mut env = Environment::default();
    env.set_option("maxHeartbeats".into(), Some(HEARTBEAT_LIMIT.to_string()));
    env.set_option(
        "tcMaxCacheEntries".into(),
        Some(CACHE_ENTRY_LIMIT.to_string()),
    );
    install_into(&mut env)?;
    Ok(env)
}

/// Install this checked vocabulary into the caller's existing environment.
///
/// All twenty owned `TrustIR.Eval.*` declaration names are checked for
/// collisions before **any** mutation, including prerequisite initialization.
/// An occupied name rejects even if its declaration is identical. This is not
/// an idempotent installer or a way to import unchecked theorem claims.
///
/// Existing declarations and environment options are retained; the environment
/// is neither cloned nor replaced. Prerequisite initializers and rooted audits
/// use the caller's resource options. Cache thresholds are per-cache trimming
/// thresholds, not total memory limits.
///
/// After the collision preflight, initialization or proof checking can still
/// fail, leaving a partially extended environment. **Discard the environment on
/// such an error.** This API is not a transaction, does not roll back, and grants
/// no source-translation, Core, or native-execution authority.
pub fn install_into(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    for name in DEFINITIONS.iter().chain(THEOREMS) {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    env.init_eq().map_err(|e| error("Eq", e))?;
    env.init_bool().map_err(|e| error("Bool", e))?;
    env.init_prod().map_err(|e| error("Prod", e))?;
    env.init_except_t().map_err(|e| error("Except", e))?;
    install_definitions(env)?;
    install_bind_congr(env)?;
    install_bind_assoc(env)?;
    install_branch_congr(env)?;
    install_force_capture(env)?;
    install_force_congr(env)?;
    install_cps_definitions(env)?;
    install_from_to_cps(env)?;
    install_to_cps_bind(env)?;
    install_to_cps_branch(env)?;
    install_to_cps_force_capture(env)?;
    for theorem in THEOREMS {
        recheck_theorem(env, theorem)?;
    }
    Ok(())
}

fn recheck_theorem(env: &Environment, theorem: &str) -> Result<(), SemanticEvaluationError> {
    let name = Name::from_string(theorem);
    let info = env
        .get_const(&name)
        .ok_or_else(|| error(theorem, "missing theorem"))?;
    if info.kind != ConstantKind::Theorem {
        return Err(error(theorem, "declaration is not a theorem"));
    }
    let proof = info
        .value
        .as_ref()
        .ok_or_else(|| error(theorem, "missing proof"))?;
    let reference = Expr::const_(
        name,
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let audit = env.audit_certification(&info.type_, &reference);
    if !audit.issues.is_empty() {
        return Err(error(theorem, audit.issues));
    }
    let mut checker = TypeChecker::with_mode(env, env.mode());
    checker.set_heartbeat_limit(
        env.get_option("maxHeartbeats")
            .and_then(Option::as_ref)
            .and_then(|value| value.parse().ok())
            .unwrap_or(HEARTBEAT_LIMIT),
    );
    checker.set_max_cache_entries(
        env.get_option("tcMaxCacheEntries")
            .and_then(Option::as_ref)
            .and_then(|value| value.parse().ok())
            .unwrap_or(CACHE_ENTRY_LIMIT),
    );
    checker
        .check_type(proof, &info.type_)
        .map_err(|e| error(theorem, e))?;
    Ok(())
}

// Trusted declaration construction uses fresh locals, closed by the public
// capture-avoiding Expr primitive. These locals are never accepted from a proof
// payload. One allocator spans each declaration, including its nested binders.
#[derive(Clone)]
struct Local {
    id: FVarId,
    ty: Expr,
    term: Expr,
}

impl Local {
    fn lam(&self, body: Expr) -> Expr {
        Expr::lam(
            BinderInfo::Default,
            self.ty.clone(),
            body.abstract_fvar(self.id),
        )
    }
    fn pi(&self, body: Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.ty.clone(),
            body.abstract_fvar(self.id),
        )
    }
}

#[derive(Default)]
struct Scope {
    next: u64,
}

impl Scope {
    fn local(&mut self, ty: Expr) -> Local {
        let id = FVarId::new(self.next);
        self.next += 1;
        Local {
            id,
            ty,
            term: Expr::fvar(id),
        }
    }
    fn types<const N: usize>(&mut self) -> [Local; N] {
        std::array::from_fn(|_| self.local(type_u()))
    }
}

fn u() -> Level {
    Level::param(Name::from_string("u"))
}
fn type_u() -> Expr {
    Expr::sort(Level::succ(u()))
}
fn c(name: &str) -> Expr {
    // Our declarations share one universe. Clean's Except family has separate
    // error/value universes; instantiate both at our existing universe.
    let levels = match name {
        "Except" | "Except.ok" | "Except.error" => vec![u(), u()],
        _ => vec![u()],
    };
    Expr::const_(Name::from_string(name), levels)
}
fn apps(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn prod(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod"), vec![u(), u()]),
        [a.clone(), b.clone()],
    )
}
fn pair(a: &Expr, b: &Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod.mk"), vec![u(), u()]),
        [a.clone(), b.clone(), x, y],
    )
}
fn projection(index: usize, a: &Expr, b: &Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string(if index == 0 { "Prod.fst" } else { "Prod.snd" }),
            vec![u(), u()],
        ),
        [a.clone(), b.clone(), value],
    )
}
fn outcome(e: &Expr, a: &Expr) -> Expr {
    apps("Except", [e.clone(), a.clone()])
}
fn result(s: &Expr, e: &Expr, a: &Expr) -> Expr {
    prod(s, &outcome(e, a))
}
fn run(s: &Expr, e: &Expr, a: &Expr) -> Expr {
    apps(RUN, [s.clone(), e.clone(), a.clone()])
}
fn bind(s: &Expr, e: &Expr, a: &Expr, b: &Expr, m: Expr, k: Expr, state: Expr) -> Expr {
    apps(
        BIND,
        [s.clone(), e.clone(), a.clone(), b.clone(), m, k, state],
    )
}
fn eq(ty: &Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(u())]),
        [ty.clone(), left, right],
    )
}
fn refl(ty: &Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(u())]),
        [ty.clone(), value],
    )
}
fn lams(vars: &[Local], body: Expr) -> Expr {
    vars.iter().rev().fold(body, |body, var| var.lam(body))
}
fn pis(vars: &[Local], body: Expr) -> Expr {
    vars.iter().rev().fold(body, |body, var| var.pi(body))
}

fn add(
    env: &mut Environment,
    name: &str,
    vars: &[Local],
    ty: Expr,
    body: Expr,
    theorem: bool,
) -> Result<(), SemanticEvaluationError> {
    let type_ = pis(vars, ty);
    let value = lams(vars, body);
    let declaration = if theorem {
        Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![Name::from_string("u")],
            type_,
            value,
        }
    } else {
        Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![Name::from_string("u")],
            type_,
            value,
            is_reducible: true,
        }
    };
    env.add_decl(declaration).map_err(|e| error(name, e))
}

/// Eliminate a result pair into `motive pair`, without inspecting values or
/// dropping either the updated state or the error payload.
fn result_cases(
    s: &Expr,
    e: &Expr,
    a: &Expr,
    motive: Expr,
    arm: Expr,
    value: Expr,
    prop: bool,
) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Prod.rec"),
            vec![
                if prop {
                    Level::zero()
                } else {
                    Level::succ(u())
                },
                u(),
                u(),
            ],
        ),
        [s.clone(), outcome(e, a), motive, arm, value],
    )
}
fn outcome_cases(
    e: &Expr,
    a: &Expr,
    motive: Expr,
    error_arm: Expr,
    ok_arm: Expr,
    value: Expr,
    prop: bool,
) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Except.rec"),
            vec![
                if prop {
                    Level::zero()
                } else {
                    Level::succ(u())
                },
                u(),
                u(),
            ],
        ),
        [e.clone(), a.clone(), motive, error_arm, ok_arm, value],
    )
}

fn install_definitions(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a] = sc.types();
    add(
        env,
        RUN,
        &[s.clone(), e.clone(), a.clone()],
        type_u(),
        Expr::arrow(s.term.clone(), result(&s.term, &e.term, &a.term)),
        false,
    )?;
    for (name, success) in [(PURE, true), (FAIL, false)] {
        let value = sc.local(if success {
            a.term.clone()
        } else {
            e.term.clone()
        });
        let state = sc.local(s.term.clone());
        let wrapped = apps(
            if success { "Except.ok" } else { "Except.error" },
            [e.term.clone(), a.term.clone(), value.term.clone()],
        );
        let body = state.lam(pair(
            &s.term,
            &outcome(&e.term, &a.term),
            state.term.clone(),
            wrapped,
        ));
        add(
            env,
            name,
            &[s.clone(), e.clone(), a.clone(), value],
            run(&s.term, &e.term, &a.term),
            body,
            false,
        )?;
    }

    let b = sc.local(type_u());
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let k = sc.local(Expr::arrow(a.term.clone(), run(&s.term, &e.term, &b.term)));
    let state = sc.local(s.term.clone());
    let r = sc.local(result(&s.term, &e.term, &a.term));
    let next_state = sc.local(s.term.clone());
    let o = sc.local(outcome(&e.term, &a.term));
    let err = sc.local(e.term.clone());
    let value = sc.local(a.term.clone());
    let rty = result(&s.term, &e.term, &b.term);
    let error_arm = err.lam(pair(
        &s.term,
        &outcome(&e.term, &b.term),
        next_state.term.clone(),
        apps(
            "Except.error",
            [e.term.clone(), b.term.clone(), err.term.clone()],
        ),
    ));
    let ok_arm = value.lam(Expr::apps(
        k.term.clone(),
        [value.term.clone(), next_state.term.clone()],
    ));
    let match_outcome = outcome_cases(
        &e.term,
        &a.term,
        o.lam(rty.clone()),
        error_arm,
        ok_arm,
        o.term.clone(),
        false,
    );
    let body = state.lam(result_cases(
        &s.term,
        &e.term,
        &a.term,
        r.lam(rty),
        lams(&[next_state, o], match_outcome),
        Expr::app(m.term.clone(), state.term.clone()),
        false,
    ));
    let ret = run(&s.term, &e.term, &b.term);
    add(
        env,
        BIND,
        &[s.clone(), e.clone(), a.clone(), b, m, k],
        ret,
        body,
        false,
    )?;
    install_branch_and_thunks(env)
}

// The remaining laws are registered below; these are proof terms, not verifier
// callbacks or producer-supplied semantic equations.
fn branch(s: &Expr, e: &Expr, a: &Expr, condition: Expr, yes: Expr, no: Expr, state: Expr) -> Expr {
    apps(
        BRANCH,
        [s.clone(), e.clone(), a.clone(), condition, yes, no, state],
    )
}

fn bool_cases(motive: Expr, no: Expr, yes: Expr, condition: Expr, prop: bool) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![if prop {
                Level::zero()
            } else {
                Level::succ(u())
            }],
        ),
        [motive, no, yes, condition],
    )
}

fn code_ty(s: &Expr, e: &Expr, a: &Expr, context: &Expr, lexical: &Expr) -> Expr {
    Expr::arrow(lexical.clone(), Expr::arrow(context.clone(), run(s, e, a)))
}

fn install_branch_and_thunks(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, context, lexical] = sc.types();
    let condition = sc.local(bool_ty());
    let yes = sc.local(run(&s.term, &e.term, &a.term));
    let no = sc.local(yes.ty.clone());
    let state = sc.local(s.term.clone());
    let flag = sc.local(bool_ty());
    let body = state.lam(bool_cases(
        flag.lam(result(&s.term, &e.term, &a.term)),
        Expr::app(no.term.clone(), state.term.clone()),
        Expr::app(yes.term.clone(), state.term.clone()),
        condition.term.clone(),
        false,
    ));
    add(
        env,
        BRANCH,
        &[s.clone(), e.clone(), a.clone(), condition, yes, no],
        run(&s.term, &e.term, &a.term),
        body,
        false,
    )?;

    let types = [
        s.clone(),
        e.clone(),
        a.clone(),
        context.clone(),
        lexical.clone(),
    ];
    let code_type = code_ty(&s.term, &e.term, &a.term, &context.term, &lexical.term);
    let thunk_type = apps(THUNK, types.iter().map(|v| v.term.clone()));
    add(
        env,
        THUNK,
        &types,
        type_u(),
        prod(&lexical.term, &code_type),
        false,
    )?;
    let code = sc.local(code_type.clone());
    let lex = sc.local(lexical.term.clone());
    let mut vars = types.to_vec();
    vars.extend([code.clone(), lex.clone()]);
    add(
        env,
        CAPTURE,
        &vars,
        thunk_type.clone(),
        pair(
            &lexical.term,
            &code_type,
            lex.term.clone(),
            code.term.clone(),
        ),
        false,
    )?;

    let thunk = sc.local(thunk_type);
    let ctx = sc.local(context.term.clone());
    let state = sc.local(s.term.clone());
    let captured_env = projection(0, &lexical.term, &code_type, thunk.term.clone());
    let captured_code = projection(1, &lexical.term, &code_type, thunk.term.clone());
    let body = Expr::apps(
        captured_code,
        [captured_env, ctx.term.clone(), state.term.clone()],
    );
    let mut vars = types.to_vec();
    vars.extend([thunk, ctx, state]);
    add(
        env,
        FORCE,
        &vars,
        result(&s.term, &e.term, &a.term),
        body,
        false,
    )
}

// Resume an already evaluated pair by a definitional instance of bind. The
// ignored initial state is not a snapshot: the pair carries the current state.
fn resume(
    sc: &mut Scope,
    s: &Expr,
    e: &Expr,
    a: &Expr,
    b: &Expr,
    pair: Expr,
    k: Expr,
    state: Expr,
) -> Expr {
    let ignored = sc.local(s.clone());
    bind(s, e, a, b, ignored.lam(pair), k, state)
}

fn pointwise(sc: &mut Scope, s: &Expr, e: &Expr, a: &Expr, left: &Expr, right: &Expr) -> Expr {
    let state = sc.local(s.clone());
    state.pi(eq(
        &result(s, e, a),
        Expr::app(left.clone(), state.term.clone()),
        Expr::app(right.clone(), state.term.clone()),
    ))
}

fn trans(ty: &Expr, left: Expr, middle: Expr, right: Expr, first: Expr, second: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(u())]),
        [ty.clone(), left, middle, right, first, second],
    )
}

fn congr_arg(input: &Expr, output: &Expr, left: Expr, right: Expr, f: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(u()), Level::succ(u())],
        ),
        [input.clone(), output.clone(), left, right, f, proof],
    )
}

fn install_bind_congr(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, b] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let n = sc.local(m.ty.clone());
    let k = sc.local(Expr::arrow(a.term.clone(), run(&s.term, &e.term, &b.term)));
    let l = sc.local(k.ty.clone());
    let hm_ty = pointwise(&mut sc, &s.term, &e.term, &a.term, &m.term, &n.term);
    let hm = sc.local(hm_ty);
    let v = sc.local(a.term.clone());
    let hk_ty = v.pi(pointwise(
        &mut sc,
        &s.term,
        &e.term,
        &b.term,
        &Expr::app(k.term.clone(), v.term.clone()),
        &Expr::app(l.term.clone(), v.term.clone()),
    ));
    let hk = sc.local(hk_ty);
    let state = sc.local(s.term.clone());
    let left = bind(
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        m.term.clone(),
        k.term.clone(),
        state.term.clone(),
    );
    let middle = bind(
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        n.term.clone(),
        k.term.clone(),
        state.term.clone(),
    );
    let right = bind(
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        n.term.clone(),
        l.term.clone(),
        state.term.clone(),
    );
    let r_a = result(&s.term, &e.term, &a.term);
    let r_b = result(&s.term, &e.term, &b.term);
    let r = sc.local(r_a.clone());
    let step_k = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        r.term.clone(),
        k.term.clone(),
        state.term.clone(),
    );
    let step_l = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        r.term.clone(),
        l.term.clone(),
        state.term.clone(),
    );
    let first = congr_arg(
        &r_a,
        &r_b,
        Expr::app(m.term.clone(), state.term.clone()),
        Expr::app(n.term.clone(), state.term.clone()),
        r.lam(step_k.clone()),
        Expr::app(hm.term.clone(), state.term.clone()),
    );
    let motive = r.lam(eq(&r_b, step_k, step_l));
    let next = sc.local(s.term.clone());
    let o = sc.local(outcome(&e.term, &a.term));
    let concrete = pair(&s.term, &o.ty, next.term.clone(), o.term.clone());
    let arm_left = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        concrete.clone(),
        k.term.clone(),
        state.term.clone(),
    );
    let arm_right = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        concrete,
        l.term.clone(),
        state.term.clone(),
    );
    let err = sc.local(e.term.clone());
    let value = sc.local(a.term.clone());
    let err_result = pair(
        &s.term,
        &outcome(&e.term, &b.term),
        next.term.clone(),
        apps(
            "Except.error",
            [e.term.clone(), b.term.clone(), err.term.clone()],
        ),
    );
    let split = outcome_cases(
        &e.term,
        &a.term,
        o.lam(eq(&r_b, arm_left, arm_right)),
        err.lam(refl(&r_b, err_result)),
        value.lam(Expr::apps(
            hk.term.clone(),
            [value.term.clone(), next.term.clone()],
        )),
        o.term.clone(),
        true,
    );
    let second = result_cases(
        &s.term,
        &e.term,
        &a.term,
        motive,
        lams(&[next, o], split),
        Expr::app(n.term.clone(), state.term.clone()),
        true,
    );
    let statement = eq(&r_b, left.clone(), right.clone());
    let proof = trans(&r_b, left, middle, right, first, second);
    add(
        env,
        BIND_CONGR,
        &[s, e, a, b, m, n, k, l, hm, hk, state],
        statement,
        proof,
        true,
    )
}

fn install_bind_assoc(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, b, d] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let k = sc.local(Expr::arrow(a.term.clone(), run(&s.term, &e.term, &b.term)));
    let h = sc.local(Expr::arrow(b.term.clone(), run(&s.term, &e.term, &d.term)));
    let state = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let st = sc.local(s.term.clone());
    let kh = lams(
        &[value.clone(), st.clone()],
        bind(
            &s.term,
            &e.term,
            &b.term,
            &d.term,
            Expr::app(k.term.clone(), value.term.clone()),
            h.term.clone(),
            st.term.clone(),
        ),
    );
    let mk = apps(
        BIND,
        [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            b.term.clone(),
            m.term.clone(),
            k.term.clone(),
        ],
    );
    let left = bind(
        &s.term,
        &e.term,
        &b.term,
        &d.term,
        mk,
        h.term.clone(),
        state.term.clone(),
    );
    let right = bind(
        &s.term,
        &e.term,
        &a.term,
        &d.term,
        m.term.clone(),
        kh.clone(),
        state.term.clone(),
    );
    let r_d = result(&s.term, &e.term, &d.term);
    let r = sc.local(result(&s.term, &e.term, &a.term));
    let rk = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        r.term.clone(),
        k.term.clone(),
        state.term.clone(),
    );
    let rkh = resume(
        &mut sc,
        &s.term,
        &e.term,
        &b.term,
        &d.term,
        rk,
        h.term.clone(),
        state.term.clone(),
    );
    let rr = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &d.term,
        r.term.clone(),
        kh.clone(),
        state.term.clone(),
    );
    let motive = r.lam(eq(&r_d, rkh, rr));
    let next = sc.local(s.term.clone());
    let o = sc.local(outcome(&e.term, &a.term));
    let concrete = pair(&s.term, &o.ty, next.term.clone(), o.term.clone());
    let rk = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &b.term,
        concrete.clone(),
        k.term.clone(),
        state.term.clone(),
    );
    let arm_left = resume(
        &mut sc,
        &s.term,
        &e.term,
        &b.term,
        &d.term,
        rk,
        h.term.clone(),
        state.term.clone(),
    );
    let arm_right = resume(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        &d.term,
        concrete,
        kh,
        state.term.clone(),
    );
    let err = sc.local(e.term.clone());
    let err_result = pair(
        &s.term,
        &outcome(&e.term, &d.term),
        next.term.clone(),
        apps(
            "Except.error",
            [e.term.clone(), d.term.clone(), err.term.clone()],
        ),
    );
    let ok_result = bind(
        &s.term,
        &e.term,
        &b.term,
        &d.term,
        Expr::app(k.term.clone(), value.term.clone()),
        h.term.clone(),
        next.term.clone(),
    );
    let split = outcome_cases(
        &e.term,
        &a.term,
        o.lam(eq(&r_d, arm_left, arm_right)),
        err.lam(refl(&r_d, err_result)),
        value.lam(refl(&r_d, ok_result)),
        o.term.clone(),
        true,
    );
    let proof = result_cases(
        &s.term,
        &e.term,
        &a.term,
        motive,
        lams(&[next, o], split),
        Expr::app(m.term.clone(), state.term.clone()),
        true,
    );
    add(
        env,
        BIND_ASSOC,
        &[s, e, a, b, d, m, k, h, state],
        eq(&r_d, left, right),
        proof,
        true,
    )
}

fn install_branch_congr(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a] = sc.types();
    let condition = sc.local(bool_ty());
    let yes = sc.local(run(&s.term, &e.term, &a.term));
    let yes2 = sc.local(yes.ty.clone());
    let no = sc.local(yes.ty.clone());
    let no2 = sc.local(yes.ty.clone());
    let hy_ty = pointwise(&mut sc, &s.term, &e.term, &a.term, &yes.term, &yes2.term);
    let hy = sc.local(hy_ty);
    let hn_ty = pointwise(&mut sc, &s.term, &e.term, &a.term, &no.term, &no2.term);
    let hn = sc.local(hn_ty);
    let state = sc.local(s.term.clone());
    let flag = sc.local(bool_ty());
    let left = branch(
        &s.term,
        &e.term,
        &a.term,
        flag.term.clone(),
        yes.term.clone(),
        no.term.clone(),
        state.term.clone(),
    );
    let right = branch(
        &s.term,
        &e.term,
        &a.term,
        flag.term.clone(),
        yes2.term.clone(),
        no2.term.clone(),
        state.term.clone(),
    );
    let goal = eq(&result(&s.term, &e.term, &a.term), left, right);
    let motive = flag.lam(goal.clone());
    let proof = bool_cases(
        motive,
        Expr::app(hn.term.clone(), state.term.clone()),
        Expr::app(hy.term.clone(), state.term.clone()),
        condition.term.clone(),
        true,
    );
    let statement = goal.subst_fvar(flag.id, &condition.term);
    add(
        env,
        BRANCH_CONGR,
        &[s, e, a, condition, yes, yes2, no, no2, hy, hn, state],
        statement,
        proof,
        true,
    )
}

fn install_force_capture(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, context, lexical] = sc.types();
    let code = sc.local(code_ty(
        &s.term,
        &e.term,
        &a.term,
        &context.term,
        &lexical.term,
    ));
    let lex = sc.local(lexical.term.clone());
    let ctx = sc.local(context.term.clone());
    let state = sc.local(s.term.clone());
    let mut types = vec![
        s.term.clone(),
        e.term.clone(),
        a.term.clone(),
        context.term.clone(),
        lexical.term.clone(),
    ];
    let mut capture = types.clone();
    capture.extend([code.term.clone(), lex.term.clone()]);
    types.extend([apps(CAPTURE, capture), ctx.term.clone(), state.term.clone()]);
    let lhs = apps(FORCE, types);
    let rhs = Expr::apps(
        code.term.clone(),
        [lex.term.clone(), ctx.term.clone(), state.term.clone()],
    );
    let r = result(&s.term, &e.term, &a.term);
    let statement = eq(&r, lhs, rhs.clone());
    add(
        env,
        FORCE_CAPTURE,
        &[s, e, a, context, lexical, code, lex, ctx, state],
        statement,
        refl(&r, rhs),
        true,
    )
}

fn install_force_congr(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, context, source_lexical, target_lexical] = sc.types();
    let source = sc.local(code_ty(
        &s.term,
        &e.term,
        &a.term,
        &context.term,
        &source_lexical.term,
    ));
    let target = sc.local(code_ty(
        &s.term,
        &e.term,
        &a.term,
        &context.term,
        &target_lexical.term,
    ));
    let source_lex = sc.local(source_lexical.term.clone());
    let target_lex = sc.local(target_lexical.term.clone());
    let ctx = sc.local(context.term.clone());
    let state = sc.local(s.term.clone());
    let r = result(&s.term, &e.term, &a.term);
    let hypothesis = sc.local(pis(
        &[ctx.clone(), state.clone()],
        eq(
            &r,
            Expr::apps(
                source.term.clone(),
                [
                    source_lex.term.clone(),
                    ctx.term.clone(),
                    state.term.clone(),
                ],
            ),
            Expr::apps(
                target.term.clone(),
                [
                    target_lex.term.clone(),
                    ctx.term.clone(),
                    state.term.clone(),
                ],
            ),
        ),
    ));
    let force_capture = |lexical: &Local, code: &Local, lex: &Local| {
        let types = [
            s.term.clone(),
            e.term.clone(),
            a.term.clone(),
            context.term.clone(),
            lexical.term.clone(),
        ];
        let captured = apps(
            CAPTURE,
            types
                .iter()
                .cloned()
                .chain([code.term.clone(), lex.term.clone()]),
        );
        apps(
            FORCE,
            types
                .into_iter()
                .chain([captured, ctx.term.clone(), state.term.clone()]),
        )
    };
    let statement = eq(
        &r,
        force_capture(&source_lexical, &source, &source_lex),
        force_capture(&target_lexical, &target, &target_lex),
    );
    // Both capture/force pairs reduce to their actual code applications. The
    // hypothesis supplies their pointwise equality; no extensionality axiom or
    // callback identity assumption is used to manufacture it.
    let proof = Expr::apps(
        hypothesis.term.clone(),
        [ctx.term.clone(), state.term.clone()],
    );
    add(
        env,
        FORCE_CONGR,
        &[
            s,
            e,
            a,
            context,
            source_lexical,
            target_lexical,
            source,
            target,
            source_lex,
            target_lex,
            hypothesis,
            ctx,
            state,
        ],
        statement,
        proof,
        true,
    )
}

fn continuation(s: &Expr, a: &Expr, answer: &Expr) -> Expr {
    Expr::arrow(s.clone(), Expr::arrow(a.clone(), answer.clone()))
}

fn cps(s: &Expr, e: &Expr, a: &Expr, answer: &Expr) -> Expr {
    apps(CPS, [s.clone(), e.clone(), a.clone(), answer.clone()])
}

fn to_cps(
    s: &Expr,
    e: &Expr,
    a: &Expr,
    answer: &Expr,
    m: Expr,
    state: Expr,
    ok: Expr,
    err: Expr,
) -> Expr {
    apps(
        TO_CPS,
        [
            s.clone(),
            e.clone(),
            a.clone(),
            answer.clone(),
            m,
            state,
            ok,
            err,
        ],
    )
}

fn install_cps_definitions(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, answer] = sc.types();
    let ok_ty = continuation(&s.term, &a.term, &answer.term);
    let err_ty = continuation(&s.term, &e.term, &answer.term);
    add(
        env,
        CPS,
        &[s.clone(), e.clone(), a.clone(), answer.clone()],
        type_u(),
        Expr::arrow(
            s.term.clone(),
            Expr::arrow(
                ok_ty.clone(),
                Expr::arrow(err_ty.clone(), answer.term.clone()),
            ),
        ),
        false,
    )?;
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let state = sc.local(s.term.clone());
    let ok = sc.local(ok_ty);
    let err = sc.local(err_ty);
    let r = sc.local(result(&s.term, &e.term, &a.term));
    let next = sc.local(s.term.clone());
    let o = sc.local(outcome(&e.term, &a.term));
    let value = sc.local(a.term.clone());
    let failure = sc.local(e.term.clone());
    let split = outcome_cases(
        &e.term,
        &a.term,
        o.lam(answer.term.clone()),
        failure.lam(Expr::apps(
            err.term.clone(),
            [next.term.clone(), failure.term.clone()],
        )),
        value.lam(Expr::apps(
            ok.term.clone(),
            [next.term.clone(), value.term.clone()],
        )),
        o.term.clone(),
        false,
    );
    let body = result_cases(
        &s.term,
        &e.term,
        &a.term,
        r.lam(answer.term.clone()),
        lams(&[next, o], split),
        Expr::app(m.term.clone(), state.term.clone()),
        false,
    );
    let converted_ty = cps(&s.term, &e.term, &a.term, &answer.term);
    add(
        env,
        TO_CPS,
        &[s.clone(), e.clone(), a.clone(), answer, m],
        converted_ty,
        lams(&[state.clone(), ok, err], body),
        false,
    )?;

    // The answer is now fixed to the actual state/outcome observation. These
    // final continuations preserve both state and payload, including failure.
    let rty = result(&s.term, &e.term, &a.term);
    let f = sc.local(cps(&s.term, &e.term, &a.term, &rty));
    let next = sc.local(s.term.clone());
    let final_arm = |payload: &Local, constructor| {
        lams(
            &[next.clone(), payload.clone()],
            pair(
                &s.term,
                &outcome(&e.term, &a.term),
                next.term.clone(),
                apps(
                    constructor,
                    [e.term.clone(), a.term.clone(), payload.term.clone()],
                ),
            ),
        )
    };
    let body = state.lam(Expr::apps(
        f.term.clone(),
        [
            state.term.clone(),
            final_arm(&value, "Except.ok"),
            final_arm(&failure, "Except.error"),
        ],
    ));
    add(
        env,
        FROM_CPS,
        &[s.clone(), e.clone(), a.clone(), f],
        run(&s.term, &e.term, &a.term),
        body,
        false,
    )
}

// Build actual Prod/Except elimination proofs for an equation about an
// arbitrary evaluated pair. Both branches retain the pair's updated state.
fn prove_result_cases(
    sc: &mut Scope,
    s: &Expr,
    e: &Expr,
    a: &Expr,
    evaluated: Expr,
    equation: impl Fn(Expr) -> Expr,
    error_proof: impl Fn(Expr, Expr) -> Expr,
    ok_proof: impl Fn(Expr, Expr) -> Expr,
) -> Expr {
    let r = sc.local(result(s, e, a));
    let next = sc.local(s.clone());
    let o = sc.local(outcome(e, a));
    let failure = sc.local(e.clone());
    let value = sc.local(a.clone());
    let split = outcome_cases(
        e,
        a,
        o.lam(equation(pair(s, &o.ty, next.term.clone(), o.term.clone()))),
        failure.lam(error_proof(next.term.clone(), failure.term.clone())),
        value.lam(ok_proof(next.term.clone(), value.term.clone())),
        o.term.clone(),
        true,
    );
    result_cases(
        s,
        e,
        a,
        r.lam(equation(r.term.clone())),
        lams(&[next, o], split),
        evaluated,
        true,
    )
}

fn install_from_to_cps(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let state = sc.local(s.term.clone());
    let ignored = sc.local(s.term.clone());
    let rty = result(&s.term, &e.term, &a.term);
    let roundtrip = |computation| {
        let converted = apps(
            TO_CPS,
            [
                s.term.clone(),
                e.term.clone(),
                a.term.clone(),
                rty.clone(),
                computation,
            ],
        );
        apps(
            FROM_CPS,
            [
                s.term.clone(),
                e.term.clone(),
                a.term.clone(),
                converted,
                state.term.clone(),
            ],
        )
    };
    let evaluated = Expr::app(m.term.clone(), state.term.clone());
    let arm = |next, payload, constructor| {
        refl(
            &rty,
            pair(
                &s.term,
                &outcome(&e.term, &a.term),
                next,
                apps(constructor, [e.term.clone(), a.term.clone(), payload]),
            ),
        )
    };
    let proof = prove_result_cases(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        evaluated.clone(),
        |r| eq(&rty, roundtrip(ignored.lam(r.clone())), r),
        |next, failure| arm(next, failure, "Except.error"),
        |next, value| arm(next, value, "Except.ok"),
    );
    let statement = eq(&rty, roundtrip(m.term.clone()), evaluated);
    add(
        env,
        FROM_TO_CPS,
        &[s, e, a, m, state],
        statement,
        proof,
        true,
    )
}

fn install_to_cps_bind(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, b, answer] = sc.types();
    let m = sc.local(run(&s.term, &e.term, &a.term));
    let k = sc.local(Expr::arrow(a.term.clone(), run(&s.term, &e.term, &b.term)));
    let state = sc.local(s.term.clone());
    let ok = sc.local(continuation(&s.term, &b.term, &answer.term));
    let err = sc.local(continuation(&s.term, &e.term, &answer.term));
    let next = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let continued = |next, value| {
        to_cps(
            &s.term,
            &e.term,
            &b.term,
            &answer.term,
            Expr::app(k.term.clone(), value),
            next,
            ok.term.clone(),
            err.term.clone(),
        )
    };
    let cps_k = lams(
        &[next.clone(), value.clone()],
        continued(next.term.clone(), value.term.clone()),
    );
    let equation = |computation: Expr| {
        let sequential = apps(
            BIND,
            [
                s.term.clone(),
                e.term.clone(),
                a.term.clone(),
                b.term.clone(),
                computation.clone(),
                k.term.clone(),
            ],
        );
        eq(
            &answer.term,
            to_cps(
                &s.term,
                &e.term,
                &b.term,
                &answer.term,
                sequential,
                state.term.clone(),
                ok.term.clone(),
                err.term.clone(),
            ),
            to_cps(
                &s.term,
                &e.term,
                &a.term,
                &answer.term,
                computation,
                state.term.clone(),
                cps_k.clone(),
                err.term.clone(),
            ),
        )
    };
    let ignored = sc.local(s.term.clone());
    let proof = prove_result_cases(
        &mut sc,
        &s.term,
        &e.term,
        &a.term,
        Expr::app(m.term.clone(), state.term.clone()),
        |r| equation(ignored.lam(r)),
        |next, failure| refl(&answer.term, Expr::apps(err.term.clone(), [next, failure])),
        |next, value| refl(&answer.term, continued(next, value)),
    );
    let statement = equation(m.term.clone());
    add(
        env,
        TO_CPS_BIND,
        &[s, e, a, b, answer, m, k, state, ok, err],
        statement,
        proof,
        true,
    )
}

fn install_to_cps_branch(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, answer] = sc.types();
    let condition = sc.local(bool_ty());
    let yes = sc.local(run(&s.term, &e.term, &a.term));
    let no = sc.local(yes.ty.clone());
    let state = sc.local(s.term.clone());
    let ok = sc.local(continuation(&s.term, &a.term, &answer.term));
    let err = sc.local(continuation(&s.term, &e.term, &answer.term));
    let flag = sc.local(bool_ty());
    let ignored = sc.local(bool_ty());
    let convert = |m| {
        to_cps(
            &s.term,
            &e.term,
            &a.term,
            &answer.term,
            m,
            state.term.clone(),
            ok.term.clone(),
            err.term.clone(),
        )
    };
    let equation = |flag: Expr| {
        let computation = apps(
            BRANCH,
            [
                s.term.clone(),
                e.term.clone(),
                a.term.clone(),
                flag.clone(),
                yes.term.clone(),
                no.term.clone(),
            ],
        );
        eq(
            &answer.term,
            convert(computation),
            bool_cases(
                ignored.lam(answer.term.clone()),
                convert(no.term.clone()),
                convert(yes.term.clone()),
                flag,
                false,
            ),
        )
    };
    let proof = bool_cases(
        flag.lam(equation(flag.term.clone())),
        refl(&answer.term, convert(no.term.clone())),
        refl(&answer.term, convert(yes.term.clone())),
        condition.term.clone(),
        true,
    );
    let statement = equation(condition.term.clone());
    add(
        env,
        TO_CPS_BRANCH,
        &[s, e, a, answer, condition, yes, no, state, ok, err],
        statement,
        proof,
        true,
    )
}

fn install_to_cps_force_capture(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, context, lexical, answer] = sc.types();
    let code = sc.local(code_ty(
        &s.term,
        &e.term,
        &a.term,
        &context.term,
        &lexical.term,
    ));
    let lex = sc.local(lexical.term.clone());
    let ctx = sc.local(context.term.clone());
    let state = sc.local(s.term.clone());
    let ok = sc.local(continuation(&s.term, &a.term, &answer.term));
    let err = sc.local(continuation(&s.term, &e.term, &answer.term));
    let types = [
        s.term.clone(),
        e.term.clone(),
        a.term.clone(),
        context.term.clone(),
        lexical.term.clone(),
    ];
    let captured = apps(
        CAPTURE,
        types
            .iter()
            .cloned()
            .chain([code.term.clone(), lex.term.clone()]),
    );
    let forced = apps(FORCE, types.into_iter().chain([captured, ctx.term.clone()]));
    let convert = |m| {
        to_cps(
            &s.term,
            &e.term,
            &a.term,
            &answer.term,
            m,
            state.term.clone(),
            ok.term.clone(),
            err.term.clone(),
        )
    };
    let right = convert(Expr::apps(
        code.term.clone(),
        [lex.term.clone(), ctx.term.clone()],
    ));
    let statement = eq(&answer.term, convert(forced), right.clone());
    let proof = refl(&answer.term, right);
    add(
        env,
        TO_CPS_FORCE_CAPTURE,
        &[
            s, e, a, context, lexical, answer, code, lex, ctx, state, ok, err,
        ],
        statement,
        proof,
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at_zero(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
        let levels = match name {
            "Except" | "Except.ok" | "Except.error" => vec![Level::zero(), Level::zero()],
            _ => vec![Level::zero()],
        };
        Expr::apps(Expr::const_(Name::from_string(name), levels), args)
    }

    fn truth(value: bool) -> Expr {
        Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
    }

    fn product(a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Prod"),
                vec![Level::zero(), Level::zero()],
            ),
            [a.clone(), b.clone()],
        )
    }

    fn product_value(a: &Expr, b: &Expr, x: Expr, y: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Prod.mk"),
                vec![Level::zero(), Level::zero()],
            ),
            [a.clone(), b.clone(), x, y],
        )
    }

    fn bool_result(value_type: &Expr, state: bool, success: bool, value: Expr) -> Expr {
        let out = at_zero("Except", [bool_ty(), value_type.clone()]);
        let wrapped = at_zero(
            if success { "Except.ok" } else { "Except.error" },
            [bool_ty(), value_type.clone(), value],
        );
        product_value(&bool_ty(), &out, truth(state), wrapped)
    }

    fn check_eq(env: &Environment, ty: &Expr, left: &Expr, right: &Expr) -> bool {
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [ty.clone(), left.clone(), right.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [ty.clone(), right.clone()],
        );
        let mut checker = TypeChecker::with_mode(env, env.mode());
        checker.set_heartbeat_limit(HEARTBEAT_LIMIT);
        checker.set_max_cache_entries(CACHE_ENTRY_LIMIT);
        checker.check_type(&proof, &goal).is_ok()
    }

    fn bool_result_type(value_type: &Expr) -> Expr {
        product(
            &bool_ty(),
            &at_zero("Except", [bool_ty(), value_type.clone()]),
        )
    }

    fn bool_bind(m: Expr, k: Expr, state: bool) -> Expr {
        at_zero(
            BIND,
            [
                bool_ty(),
                bool_ty(),
                bool_ty(),
                bool_ty(),
                m,
                k,
                truth(state),
            ],
        )
    }

    #[test]
    fn install_into_preserves_existing_declarations_and_caller_options() {
        let mut env = Environment::default();
        env.init_eq().unwrap();
        env.init_bool().unwrap();
        let name = Name::from_string("Consumer.retained");
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: bool_ty(),
            value: truth(true),
            is_reducible: true,
        })
        .unwrap();
        env.set_option("maxHeartbeats".into(), Some("2000000".into()));
        env.set_option("tcMaxCacheEntries".into(), Some("127".into()));
        env.set_option("consumer.option".into(), None);
        let mode = env.mode();
        let original = env.get_const(&name).unwrap().clone();

        install_into(&mut env).unwrap();

        let retained = env.get_const(&name).unwrap();
        assert_eq!(retained.kind, original.kind);
        assert_eq!(retained.type_, original.type_);
        assert_eq!(retained.value, original.value);
        assert_eq!(retained.level_params, original.level_params);
        assert_eq!(env.mode(), mode);
        assert_eq!(
            env.get_option("maxHeartbeats"),
            Some(&Some("2000000".into()))
        );
        assert_eq!(
            env.get_option("tcMaxCacheEntries"),
            Some(&Some("127".into()))
        );
        assert_eq!(env.get_option("consumer.option"), Some(&None));
        let installed: std::collections::BTreeSet<_> = env
            .constants()
            .map(|info| info.name.to_string())
            .filter(|name| name.starts_with("TrustIR.Eval."))
            .collect();
        let expected: std::collections::BTreeSet<_> = DEFINITIONS
            .iter()
            .chain(THEOREMS)
            .map(|name| (*name).to_owned())
            .collect();
        assert_eq!(expected.len(), 20);
        assert_eq!(installed, expected);
        for name in THEOREMS {
            // Exercise the real rooted audit and term checker
            // in the caller's populated environment, not just name presence.
            recheck_theorem(&env, name).unwrap();
        }
    }

    #[test]
    fn install_into_every_owned_name_collision_rejects_before_any_mutation() {
        for name in DEFINITIONS.iter().chain(THEOREMS) {
            let mut env = Environment::default();
            // This well-typed definition needs no prerequisite initialization;
            // a late collision must not install even Eq or Bool on its way out.
            env.add_decl(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::sort(Level::succ(Level::zero())),
                value: Expr::sort(Level::zero()),
                is_reducible: true,
            })
            .unwrap();
            env.set_option("maxHeartbeats".into(), Some("1".into()));
            env.set_option("tcMaxCacheEntries".into(), Some("3".into()));
            let before_generation = env.generation();
            let before_count = env.num_constants();
            let rejected = install_into(&mut env).unwrap_err();
            assert_eq!(rejected.declaration, *name);
            assert_eq!(rejected.reason, "\"owned declaration already exists\"");
            assert_eq!(env.generation(), before_generation, "{name}");
            assert_eq!(env.num_constants(), before_count, "{name}");
            assert_eq!(env.get_option("maxHeartbeats"), Some(&Some("1".into())));
            assert_eq!(env.get_option("tcMaxCacheEntries"), Some(&Some("3".into())));
        }
    }

    #[test]
    fn install_into_rejects_even_identical_previously_installed_vocabulary() {
        let mut env = build_environment().unwrap();
        let before_generation = env.generation();
        let before_count = env.num_constants();
        let rejected = install_into(&mut env).unwrap_err();
        assert_eq!(rejected.declaration, RUN);
        assert_eq!(env.generation(), before_generation);
        assert_eq!(env.num_constants(), before_count);
        assert_eq!(
            env.get_option("maxHeartbeats"),
            Some(&Some(HEARTBEAT_LIMIT.to_string()))
        );
        assert_eq!(
            env.get_option("tcMaxCacheEntries"),
            Some(&Some(CACHE_ENTRY_LIMIT.to_string()))
        );
    }

    #[test]
    fn install_into_does_not_raise_a_callers_exhausted_checking_budget() {
        let mut env = Environment::default();
        env.init_eq().unwrap();
        env.init_bool().unwrap();
        env.init_prod().unwrap();
        env.init_except_t().unwrap();
        env.set_option("maxHeartbeats".into(), Some("1".into()));
        env.set_option("tcMaxCacheEntries".into(), Some("1".into()));
        let rejected = install_into(&mut env).unwrap_err();
        assert!(
            rejected.reason.to_ascii_lowercase().contains("heartbeat"),
            "must refuse because of the actual caller budget: {rejected}"
        );
        assert_eq!(env.get_option("maxHeartbeats"), Some(&Some("1".into())));
        assert_eq!(env.get_option("tcMaxCacheEntries"), Some(&Some("1".into())));
        // Noncollision failure is explicitly not transactional: discard env.
    }

    #[test]
    fn generic_evaluation_laws_kernel_check_and_rooted_audit() {
        let env = build_environment().unwrap();
        for name in THEOREMS {
            recheck_theorem(&env, name).unwrap();
            let info = env.get_const(&Name::from_string(name)).unwrap();
            assert_eq!(info.level_params, vec![Name::from_string("u")]);
            let audit = env.audit_certification(&info.type_, &c(name));
            assert!(audit.dependencies.iter().all(|dependency| {
                let name = dependency.to_string();
                !name.starts_with("StateT")
                    && !name.starts_with("ExceptT")
                    && !name.starts_with("Monad")
                    && name != "funext"
            }));
        }
    }

    #[test]
    fn except_universe_arity_remains_kernel_checked() {
        let mut env = Environment::default();
        env.init_except_t().unwrap();
        let checker = TypeChecker::new(&env);
        for (name, arity) in [
            ("Except", 2),
            ("Except.error", 2),
            ("Except.ok", 2),
            ("Except.rec", 3),
        ] {
            let constant =
                |count| Expr::const_(Name::from_string(name), vec![Level::zero(); count]);
            assert!(checker.infer_type(&constant(arity)).is_ok(), "{name}");
            let error = checker.infer_type(&constant(arity - 1)).unwrap_err();
            assert!(
                matches!(
                    &error,
                    clean_kernel::KernelTypeError::LevelCountMismatch {
                        expected,
                        got,
                        ..
                    } if *expected == arity && *got == arity - 1
                ),
                "{name} must reject its missing universe: {error:?}"
            );
        }
    }

    #[test]
    fn sequence_preserves_updated_error_state_and_never_invokes_continuation() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let state = sc.local(bool_ty());
        // Fail after a state transition, not a pure failure at the input state.
        let computation = state.lam(bool_result(&bool_ty(), true, false, truth(false)));
        let value = sc.local(bool_ty());
        let continuation = lams(
            &[value, state],
            bool_result(&bool_ty(), false, true, truth(true)),
        );
        let applied = bool_bind(computation, continuation, false);
        let expected = bool_result(&bool_ty(), true, false, truth(false));
        let ty = bool_result_type(&bool_ty());
        assert!(check_eq(&env, &ty, &applied, &expected));
        assert!(
            !check_eq(
                &env,
                &ty,
                &applied,
                &bool_result(&bool_ty(), false, false, truth(false))
            ),
            "failure must not restore the initial state"
        );
        assert!(
            !check_eq(
                &env,
                &ty,
                &applied,
                &bool_result(&bool_ty(), true, false, truth(true))
            ),
            "failure payload is observable"
        );
        assert!(
            !check_eq(
                &env,
                &ty,
                &applied,
                &bool_result(&bool_ty(), false, true, truth(true))
            ),
            "failure must not run the continuation"
        );
    }

    #[test]
    fn branch_selects_one_computation_with_the_callers_state() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let state = sc.local(bool_ty());
        let out = at_zero("Except", [bool_ty(), bool_ty()]);
        let success = product_value(
            &bool_ty(),
            &out,
            state.term.clone(),
            at_zero("Except.ok", [bool_ty(), bool_ty(), state.term.clone()]),
        );
        let yes = state.lam(success);
        let no = state.lam(bool_result(&bool_ty(), false, false, truth(true)));
        let selected = at_zero(
            BRANCH,
            [
                bool_ty(),
                bool_ty(),
                bool_ty(),
                truth(true),
                yes.clone(),
                no.clone(),
                truth(true),
            ],
        );
        let ty = bool_result_type(&bool_ty());
        assert!(check_eq(
            &env,
            &ty,
            &selected,
            &bool_result(&bool_ty(), true, true, truth(true))
        ));
        let other = at_zero(
            BRANCH,
            [
                bool_ty(),
                bool_ty(),
                bool_ty(),
                truth(false),
                yes,
                no,
                truth(true),
            ],
        );
        assert!(check_eq(
            &env,
            &ty,
            &other,
            &bool_result(&bool_ty(), false, false, truth(true))
        ));
        assert!(!check_eq(&env, &ty, &selected, &other));
    }

    #[test]
    fn capture_retains_lexical_environment_but_accepts_dynamic_context_and_state() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let lex = sc.local(bool_ty());
        let ctx = sc.local(bool_ty());
        let state = sc.local(bool_ty());
        // A nonnumeric value exposes both independently supplied environments.
        let value_ty = product(&bool_ty(), &bool_ty());
        let value = product_value(&bool_ty(), &bool_ty(), lex.term.clone(), ctx.term.clone());
        let out_ty = at_zero("Except", [bool_ty(), value_ty.clone()]);
        let result = product_value(
            &bool_ty(),
            &out_ty,
            state.term.clone(),
            at_zero("Except.ok", [bool_ty(), value_ty.clone(), value]),
        );
        let code = lams(&[lex, ctx, state], result);
        let types = [bool_ty(), bool_ty(), value_ty.clone(), bool_ty(), bool_ty()];
        let mut capture_args = types.to_vec();
        capture_args.extend([code, truth(false)]);
        let thunk = at_zero(CAPTURE, capture_args);
        let mut force_args = types.to_vec();
        force_args.extend([thunk, truth(true), truth(true)]);
        let forced = at_zero(FORCE, force_args);
        let expected_value = product_value(&bool_ty(), &bool_ty(), truth(false), truth(true));
        let expected = bool_result(&value_ty, true, true, expected_value);
        assert!(check_eq(
            &env,
            &bool_result_type(&value_ty),
            &forced,
            &expected
        ));
        let wrong_value = product_value(&bool_ty(), &bool_ty(), truth(true), truth(true));
        assert!(
            !check_eq(
                &env,
                &bool_result_type(&value_ty),
                &forced,
                &bool_result(&value_ty, true, true, wrong_value)
            ),
            "forcing must not replace the lexical environment with the caller context"
        );
    }

    #[test]
    fn repeated_force_threads_new_state_and_is_not_memoization() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let lex = sc.local(bool_ty());
        let ctx = sc.local(bool_ty());
        let state = sc.local(bool_ty());
        let out = at_zero("Except", [bool_ty(), bool_ty()]);
        let result = product_value(
            &bool_ty(),
            &out,
            Expr::app(Expr::const_str("Bool.not"), state.term.clone()),
            at_zero("Except.ok", [bool_ty(), bool_ty(), state.term.clone()]),
        );
        let code = lams(&[lex, ctx, state], result);
        let thunk = at_zero(
            CAPTURE,
            [
                bool_ty(),
                bool_ty(),
                bool_ty(),
                bool_ty(),
                bool_ty(),
                code,
                truth(false),
            ],
        );
        let force = at_zero(
            FORCE,
            [
                bool_ty(),
                bool_ty(),
                bool_ty(),
                bool_ty(),
                bool_ty(),
                thunk,
                truth(false),
            ],
        );
        let ignored = sc.local(bool_ty());
        let twice = bool_bind(force.clone(), ignored.lam(force.clone()), false);
        let once = Expr::app(force, truth(false));
        let ty = bool_result_type(&bool_ty());
        assert!(check_eq(
            &env,
            &ty,
            &twice,
            &bool_result(&bool_ty(), false, true, truth(true))
        ));
        assert!(
            !check_eq(&env, &ty, &twice, &once),
            "reusing the first result changes both value and state"
        );
    }

    #[test]
    fn force_congruence_checks_distinct_captures_and_complete_effectful_results() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let b = bool_ty();
        let compound = product(&b, &b);
        // Both successful values and errors are compound, nonnumeric data.
        let out_ty = at_zero("Except", [compound.clone(), compound.clone()]);
        let result_ty = product(&b, &out_ty);
        let lex = sc.local(b.clone());
        let ctx = sc.local(b.clone());
        let state = sc.local(b.clone());
        let payload = product_value(&b, &b, lex.term.clone(), state.term.clone());
        let finish = |success: bool| {
            product_value(
                &b,
                &out_ty,
                Expr::app(Expr::const_str("Bool.not"), state.term.clone()),
                at_zero(
                    if success { "Except.ok" } else { "Except.error" },
                    [compound.clone(), compound.clone(), payload.clone()],
                ),
            )
        };
        let ignored_flag = sc.local(b.clone());
        let source = lams(
            &[lex, ctx.clone(), state.clone()],
            Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    ignored_flag.lam(result_ty.clone()),
                    finish(false),
                    finish(true),
                    ctx.term.clone(),
                ],
            ),
        );
        // The target code has a DIFFERENT lexical type/representation. It
        // reads the first field of a compound captured environment, not an
        // assumed identical callback or a caller-supplied state snapshot.
        let target_lex = sc.local(compound.clone());
        let projected_lex = Expr::apps(
            Expr::const_(
                Name::from_string("Prod.fst"),
                vec![Level::zero(), Level::zero()],
            ),
            [b.clone(), b.clone(), target_lex.term.clone()],
        );
        let target = lams(
            &[target_lex, ctx.clone(), state.clone()],
            Expr::apps(
                source.clone(),
                [projected_lex, ctx.term.clone(), state.term.clone()],
            ),
        );
        let source_capture = truth(false);
        let target_capture = product_value(&b, &b, truth(false), truth(true));
        let reflexivity = |value: Expr| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [result_ty.clone(), value],
            )
        };
        let related = lams(
            &[ctx.clone(), state.clone()],
            reflexivity(Expr::apps(
                target.clone(),
                [target_capture.clone(), ctx.term.clone(), state.term.clone()],
            )),
        );
        let types = [b.clone(), compound.clone(), compound.clone(), b.clone()];
        let forced = |lexical: Expr, code: Expr, capture: Expr, ctx: bool, state: bool| {
            let args: Vec<_> = types.iter().cloned().chain([lexical]).collect();
            let thunk = at_zero(CAPTURE, args.iter().cloned().chain([code, capture]));
            at_zero(
                FORCE,
                args.into_iter().chain([thunk, truth(ctx), truth(state)]),
            )
        };
        let theorem = |related: Expr, ctx: bool, state: bool| {
            at_zero(
                FORCE_CONGR,
                types.iter().cloned().chain([
                    b.clone(),
                    compound.clone(),
                    source.clone(),
                    target.clone(),
                    source_capture.clone(),
                    target_capture.clone(),
                    related,
                    truth(ctx),
                    truth(state),
                ]),
            )
        };
        let statement = |left: Expr, right: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [result_ty.clone(), left, right],
            )
        };
        for context in [false, true] {
            for current in [false, true] {
                let left = forced(
                    b.clone(),
                    source.clone(),
                    source_capture.clone(),
                    context,
                    current,
                );
                let right = forced(
                    compound.clone(),
                    target.clone(),
                    target_capture.clone(),
                    context,
                    current,
                );
                let goal = statement(left.clone(), right);
                let proof = theorem(related.clone(), context, current);
                let audit = env.audit_certification(&goal, &proof);
                assert!(audit.is_certified(), "{audit:#?}");

                for (capture, context, current) in [
                    (
                        product_value(&b, &b, truth(true), truth(true)),
                        context,
                        current,
                    ),
                    (target_capture.clone(), !context, current),
                    (target_capture.clone(), context, !current),
                ] {
                    let changed =
                        forced(compound.clone(), target.clone(), capture, context, current);
                    let audit = env.audit_certification(&statement(left.clone(), changed), &proof);
                    assert!(
                        !audit.is_certified(),
                        "capture/context/state cannot be substituted"
                    );
                }

                // Equality at one sampled state/context is not a pointwise
                // computation relation, even when this call uses that sample.
                let sampled = lams(
                    &[ctx.clone(), state.clone()],
                    reflexivity(Expr::apps(
                        target.clone(),
                        [target_capture.clone(), truth(context), truth(current)],
                    )),
                );
                let audit = env.audit_certification(&goal, &theorem(sampled, context, current));
                assert!(
                    !audit.is_certified(),
                    "a sampled equality cannot prove all force sites"
                );
            }
        }
    }

    #[test]
    fn cps_roundtrip_retains_compound_payloads_and_updated_error_state() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let b = bool_ty();
        let payload_ty = product(&b, &b);
        let out_ty = at_zero("Except", [payload_ty.clone(), payload_ty.clone()]);
        let result_ty = product(&b, &out_ty);
        let state = sc.local(b.clone());
        let payload = product_value(&b, &b, truth(false), truth(true));
        let make_result = |success, state, payload| {
            product_value(
                &b,
                &out_ty,
                state,
                at_zero(
                    if success { "Except.ok" } else { "Except.error" },
                    [payload_ty.clone(), payload_ty.clone(), payload],
                ),
            )
        };
        for success in [false, true] {
            let m = state.lam(make_result(
                success,
                Expr::app(Expr::const_str("Bool.not"), state.term.clone()),
                payload.clone(),
            ));
            let cps = at_zero(
                TO_CPS,
                [
                    b.clone(),
                    payload_ty.clone(),
                    payload_ty.clone(),
                    result_ty.clone(),
                    m.clone(),
                ],
            );
            let observed = at_zero(
                FROM_CPS,
                [
                    b.clone(),
                    payload_ty.clone(),
                    payload_ty.clone(),
                    cps,
                    truth(false),
                ],
            );
            let expected = make_result(success, truth(true), payload.clone());
            assert!(check_eq(&env, &result_ty, &observed, &expected));
            assert!(!check_eq(
                &env,
                &result_ty,
                &observed,
                &make_result(success, truth(false), payload.clone()),
            ));
            assert!(!check_eq(
                &env,
                &result_ty,
                &observed,
                &make_result(
                    success,
                    truth(true),
                    product_value(&b, &b, truth(true), truth(true))
                ),
            ));
            assert!(!check_eq(
                &env,
                &result_ty,
                &observed,
                &make_result(!success, truth(true), payload.clone()),
            ));
            // Apply the real polymorphic theorem, not merely a producer-side
            // comparison of expected expression trees.
            let proof = at_zero(
                FROM_TO_CPS,
                [
                    b.clone(),
                    payload_ty.clone(),
                    payload_ty.clone(),
                    m.clone(),
                    truth(false),
                ],
            );
            let goal = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [result_ty.clone(), observed, Expr::app(m, truth(false))],
            );
            assert!(env.audit_certification(&goal, &proof).is_certified());
        }
    }

    #[test]
    fn cps_bind_supports_distinct_answer_type_and_short_circuits_failure() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let b = bool_ty();
        let answer_ty = product(&b, &b);
        let state = sc.local(b.clone());
        let value = sc.local(b.clone());
        let out_ty = at_zero("Except", [b.clone(), b.clone()]);
        let k = lams(
            &[value.clone(), state.clone()],
            product_value(
                &b,
                &out_ty,
                Expr::app(Expr::const_str("Bool.not"), state.term.clone()),
                at_zero("Except.ok", [b.clone(), b.clone(), state.term.clone()]),
            ),
        );
        let final_arm = lams(
            &[state.clone(), value.clone()],
            product_value(&b, &b, state.term.clone(), value.term.clone()),
        );
        for success in [false, true] {
            let m = state.lam(bool_result(&b, true, success, truth(false)));
            let sequential = at_zero(
                BIND,
                [
                    b.clone(),
                    b.clone(),
                    b.clone(),
                    b.clone(),
                    m.clone(),
                    k.clone(),
                ],
            );
            let observed = at_zero(
                TO_CPS,
                [
                    b.clone(),
                    b.clone(),
                    b.clone(),
                    answer_ty.clone(),
                    sequential,
                    truth(false),
                    final_arm.clone(),
                    final_arm.clone(),
                ],
            );
            let expected = product_value(&b, &b, truth(!success), truth(success));
            assert!(check_eq(&env, &answer_ty, &observed, &expected));
            let cps_k = lams(
                &[state.clone(), value.clone()],
                at_zero(
                    TO_CPS,
                    [
                        b.clone(),
                        b.clone(),
                        b.clone(),
                        answer_ty.clone(),
                        Expr::app(k.clone(), value.term.clone()),
                        state.term.clone(),
                        final_arm.clone(),
                        final_arm.clone(),
                    ],
                ),
            );
            let rhs = at_zero(
                TO_CPS,
                [
                    b.clone(),
                    b.clone(),
                    b.clone(),
                    answer_ty.clone(),
                    m.clone(),
                    truth(false),
                    cps_k,
                    final_arm.clone(),
                ],
            );
            let proof = at_zero(
                TO_CPS_BIND,
                [
                    b.clone(),
                    b.clone(),
                    b.clone(),
                    b.clone(),
                    answer_ty.clone(),
                    m,
                    k.clone(),
                    truth(false),
                    final_arm.clone(),
                    final_arm.clone(),
                ],
            );
            let goal = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [answer_ty.clone(), observed, rhs],
            );
            assert!(env.audit_certification(&goal, &proof).is_certified());
        }
    }

    #[test]
    fn arbitrary_fixed_answer_cps_has_no_reverse_roundtrip() {
        let env = build_environment().unwrap();
        let mut sc = Scope::default();
        let b = bool_ty();
        let rty = bool_result_type(&b);
        let state = sc.local(b.clone());
        let value = sc.local(b.clone());
        let arm_ty = Expr::arrow(b.clone(), Expr::arrow(b.clone(), rty.clone()));
        let ok = sc.local(arm_ty.clone());
        let err = sc.local(arm_ty);
        let fixed = bool_result(&b, true, true, truth(true));
        // This is a valid CPS term, but it ignores both supplied continuations.
        let arbitrary = lams(&[state.clone(), ok, err], fixed.clone());
        let from = at_zero(
            FROM_CPS,
            [b.clone(), b.clone(), b.clone(), arbitrary.clone()],
        );
        let to = at_zero(TO_CPS, [b.clone(), b.clone(), b.clone(), rty.clone(), from]);
        let changed = bool_result(&b, false, false, truth(false));
        let replace = lams(&[state, value], changed.clone());
        let args = [truth(false), replace.clone(), replace];
        let original = Expr::apps(arbitrary, args.clone());
        let roundtrip = Expr::apps(to, args);
        assert!(check_eq(&env, &rty, &original, &fixed));
        assert!(check_eq(&env, &rty, &roundtrip, &changed));
        assert!(!check_eq(&env, &rty, &original, &roundtrip));
    }

    #[test]
    fn kernel_and_rooted_audit_reject_forged_law_terms_and_axioms() {
        let mut env = build_environment().unwrap();
        let info = env.get_const(&Name::from_string(BIND_ASSOC)).unwrap();
        let statement = info.type_.clone();
        assert!(
            env.add_decl(Declaration::Theorem {
                name: Name::from_string("TrustIR.Eval.bad_term"),
                level_params: vec![Name::from_string("u")],
                type_: statement.clone(),
                value: truth(true),
            })
            .is_err()
        );
        // A theorem using an unproved premise can type-check; rooted authority
        // checking must still reject it even when the premise claims a true law.
        let axiom = "TrustIR.Eval.unproved_law";
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom),
            level_params: vec![Name::from_string("u")],
            type_: statement.clone(),
        })
        .unwrap();
        let theorem = "TrustIR.Eval.axiomatic_law";
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(theorem),
            level_params: vec![Name::from_string("u")],
            type_: statement,
            value: c(axiom),
        })
        .unwrap();
        assert!(recheck_theorem(&env, theorem).is_err());
    }
}
