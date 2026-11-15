// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Normal postconditions whose observation reads the actual State AND value.
//! Error observation is the expected value; the complete raw result is retained.
use super::*;

pub const NORMAL_VALUE_OBSERVATION: &str = "TrustIR.Eval.NormalResult.value_observation";
pub const NORMAL_VALUE_OBSERVATION_POST: &str = "TrustIR.Eval.NormalResult.value_observation_post";
const OWNED: [&str; 5] = [
    NORMAL_POST,
    NORMAL_OBSERVATION,
    NORMAL_OBSERVATION_POST,
    NORMAL_VALUE_OBSERVATION,
    NORMAL_VALUE_OBSERVATION_POST,
];

/// Install the original normal-post library and these optional checked endpoints:
///
/// ```text
/// value_observation S E A M measure expected (state, error e) = expected
/// value_observation S E A M measure expected (state, ok a) = measure state a
/// value_observation_post S E A M measure expected raw
///   (h : value_observation S E A M measure expected raw = expected) :
///   post S E A (fun state value => measure state value = expected) raw
/// ```
/// S, E, A and M inhabit Type u; every argument is explicit. The equality
/// premise names this exact raw result. Neither an error frame nor a stronger
/// value-independent property follows. The original state-only declarations
/// keep their existing bodies and installer; the default environment is unchanged.
///
/// This installer owns all five names, including the base library. Select it
/// INSTEAD OF `install_normal_post_into`, before either bundle is installed.
/// Any occupied name (even an identical base declaration) rejects before any
/// initialization or mutation. This avoids treating caller-supplied names as
/// the canonical normal-post semantics. Options are preserved; discard the
/// environment on any failure after preflight. No primitive or execution
/// behavior, source admission or termination premise is supplied.
pub fn install_normal_value_post_into(
    env: &mut Environment,
) -> Result<(), SemanticEvaluationError> {
    for name in OWNED {
        if env.get_const(&Name::from_string(name)).is_some() {
            return Err(error(name, "owned declaration already exists"));
        }
    }
    install_normal_post_into(env)?;
    definition(env)?;
    law(env)?;
    recheck_theorem(env, NORMAL_VALUE_OBSERVATION_POST)?;
    let name = Name::from_string(NORMAL_VALUE_OBSERVATION_POST);
    if !env.axiom_deps(&name).is_some_and(|deps| deps.is_empty())
        || !env
            .foundational_axiom_deps(&name)
            .is_some_and(|deps| deps.is_empty())
        || !env
            .trust_marker_deps(&name)
            .is_some_and(|deps| deps.is_empty())
    {
        return Err(error(
            NORMAL_VALUE_OBSERVATION_POST,
            "missing or nonempty authority closure",
        ));
    }
    Ok(())
}
fn post(s: &Expr, e: &Expr, a: &Expr, predicate: Expr, raw: Expr) -> Expr {
    apps(
        NORMAL_POST,
        [s.clone(), e.clone(), a.clone(), predicate, raw],
    )
}
fn observation(
    s: &Expr,
    e: &Expr,
    a: &Expr,
    m: &Expr,
    measure: Expr,
    expected: Expr,
    raw: Expr,
) -> Expr {
    apps(
        NORMAL_VALUE_OBSERVATION,
        [
            s.clone(),
            e.clone(),
            a.clone(),
            m.clone(),
            measure,
            expected,
            raw,
        ],
    )
}
fn definition(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, m] = sc.types();
    let measure = sc.local(Expr::arrow(
        s.term.clone(),
        Expr::arrow(a.term.clone(), m.term.clone()),
    ));
    let expected = sc.local(m.term.clone());
    let raw = sc.local(result(&s.term, &e.term, &a.term));
    let status = sc.local(outcome(&e.term, &a.term));
    let failure = sc.local(e.term.clone());
    let value = sc.local(a.term.clone());
    let body = outcome_cases(
        &e.term,
        &a.term,
        status.lam(m.term.clone()),
        failure.lam(expected.term.clone()),
        value.lam(Expr::apps(
            measure.term.clone(),
            [
                projection(0, &s.term, &outcome(&e.term, &a.term), raw.term.clone()),
                value.term.clone(),
            ],
        )),
        projection(1, &s.term, &outcome(&e.term, &a.term), raw.term.clone()),
        false,
    );
    add(
        env,
        NORMAL_VALUE_OBSERVATION,
        &[s, e, a, m.clone(), measure, expected, raw],
        m.term,
        body,
        false,
    )
}

fn law(env: &mut Environment) -> Result<(), SemanticEvaluationError> {
    let mut sc = Scope::default();
    let [s, e, a, m] = sc.types();
    let measure = sc.local(Expr::arrow(
        s.term.clone(),
        Expr::arrow(a.term.clone(), m.term.clone()),
    ));
    let expected = sc.local(m.term.clone());
    let raw = sc.local(result(&s.term, &e.term, &a.term));
    let state = sc.local(s.term.clone());
    let value = sc.local(a.term.clone());
    let predicate = lams(
        &[state.clone(), value.clone()],
        eq(
            &m.term,
            Expr::apps(
                measure.term.clone(),
                [state.term.clone(), value.term.clone()],
            ),
            expected.term.clone(),
        ),
    );
    let equality = |raw: Expr| {
        eq(
            &m.term,
            observation(
                &s.term,
                &e.term,
                &a.term,
                &m.term,
                measure.term.clone(),
                expected.term.clone(),
                raw,
            ),
            expected.term.clone(),
        )
    };
    let implication = |raw: Expr| {
        Expr::arrow(
            equality(raw.clone()),
            post(&s.term, &e.term, &a.term, predicate.clone(), raw),
        )
    };
    let premise = sc.local(equality(raw.term.clone()));
    let major = sc.local(raw.ty.clone());
    let status = sc.local(outcome(&e.term, &a.term));
    let pair = |status| {
        pair(
            &s.term,
            &outcome(&e.term, &a.term),
            state.term.clone(),
            status,
        )
    };
    let failure = sc.local(e.term.clone());
    let failure_h = sc.local(equality(pair(apps(
        "Except.error",
        [e.term.clone(), a.term.clone(), failure.term.clone()],
    ))));
    let normal_h = sc.local(equality(pair(apps(
        "Except.ok",
        [e.term.clone(), a.term.clone(), value.term.clone()],
    ))));
    let inside = outcome_cases(
        &e.term,
        &a.term,
        status.lam(implication(pair(status.term.clone()))),
        lams(&[failure, failure_h], Expr::const_str("True.intro")),
        lams(&[value, normal_h.clone()], normal_h.term),
        status.term.clone(),
        true,
    );
    let all = result_cases(
        &s.term,
        &e.term,
        &a.term,
        major.lam(implication(major.term.clone())),
        lams(&[state, status], inside),
        raw.term.clone(),
        true,
    );
    add(
        env,
        NORMAL_VALUE_OBSERVATION_POST,
        &[
            s.clone(),
            e.clone(),
            a.clone(),
            m,
            measure,
            expected,
            raw.clone(),
            premise.clone(),
        ],
        post(&s.term, &e.term, &a.term, predicate, raw.term),
        Expr::app(all, premise.term),
        true,
    )
}

#[cfg(test)]
#[path = "semantic_evaluation_normal_value_post_tests.rs"]
mod tests;
