// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Opt-in observations only: none of these values authorize reuse or traversal.

use std::sync::Arc;

use super::{Closer, Expr, TermScopeError, TermScopeInputKindCounts, census::InputCensus};

/// Scalar cache/probe observations of the charged prefix of one closing walk.
/// These are not timings, structural identities, proof evidence or wire fields.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TermScopeCacheDiagnostics {
    /// Exact repeats of a named map on the same retained output root.
    pub named_projection_repeated_roots: usize,
    pub exact_context_hits: usize,
    pub ordinary_closed_hits: usize,
    pub named_closed_hits: usize,
    pub primary_exact_attempts: usize,
    pub spare_exact_attempts: usize,
    pub primary_outward_attempts: usize,
    pub spare_outward_attempts: usize,
    /// Additional selected named-only attempts after the original selector
    /// missed, outward first and then inward. Impossible outward depth rebases
    /// can reject without a dependency probe; every performed probe is fully
    /// charged. Neither count licenses reuse.
    pub primary_named_only_attempts: usize,
    pub spare_named_only_attempts: usize,
    pub named_only_contextual_hits: usize,
    /// Additional proof attempts for the SAME selected named-only candidate;
    /// no alternate slot is probed and no old-probe visits are refunded.
    pub uniform_shift_attempts: usize,
    pub uniform_shift_refusals: usize,
    /// Successful publication, distinct from unchanged-index named-only hits.
    pub uniform_shift_contextual_hits: usize,
    /// Charged dependency requests during uniform proof, including DAG hits.
    pub uniform_shift_dependency_visits: usize,
    /// Charged ordinary OUTPUT requests, including prunes and memo hits. These
    /// are not added to the input census or transformed input-node count.
    pub uniform_shift_output_visits: usize,
    pub uniform_shift_output_memo_hits: usize,
    pub uniform_shift_output_changed_nodes: usize,
    pub uniform_shift_composed_inputs: usize,
    pub uniform_shift_composed_cache_hits: usize,
    /// Exact nonuniform named-index projection after a paid mixed-delta refusal.
    pub named_projection_attempts: usize,
    pub named_projection_refusals: usize,
    pub named_projection_contextual_hits: usize,
    pub named_projection_dependency_visits: usize,
    pub named_projection_output_visits: usize,
    pub named_projection_output_memo_hits: usize,
    pub named_projection_output_changed_nodes: usize,
    /// Shallow completed-output node construction, never additional traversal.
    pub output_node_intern_requests: usize,
    pub output_node_intern_hits: usize,
    pub dependency_node_intern_requests: usize,
    pub dependency_node_intern_hits: usize,
    pub named_prefix_proofs: usize,
    pub named_only_ordinary_rejections: usize,
    /// Selected named-only candidates whose root minimum proves a depth
    /// underflow, rejected before any dependency probe or rebase allocation.
    pub named_only_depth_screen_rejections: usize,
    /// Selected ordinary-outward candidates whose root minimum proves a depth
    /// underflow. This rejection performs no probe, does not refund visits,
    /// and can replace a formerly charged mismatch or finite-budget refusal.
    pub ordinary_depth_screen_rejections: usize,
    pub contextual_hits: usize,
    pub contextual_absent: usize,
    pub contextual_shape_misses: usize,
    pub shape_misses_without_loose_bvars: usize,
    /// Shape-miss requests with no original loose-BVar quick flag and a
    /// declaration-free retained slot. Screening only: no dependency probe.
    pub declaration_free_primary_shape_misses: usize,
    pub declaration_free_spare_shape_misses: usize,
    /// Requests with at least one such slot at the indicated depth. A request
    /// can occur in multiple categories when its two slots have different depths.
    pub declaration_free_same_depth_shape_misses: usize,
    pub declaration_free_outward_shape_misses: usize,
    pub declaration_free_inward_shape_misses: usize,
    /// The unselected slot is shape-eligible; its dependencies are NOT probed.
    pub alternate_shape_available: usize,
    /// The selected attempt refused while the other slot was shape-eligible.
    /// This neither probes the alternate nor claims it would have succeeded.
    pub rejected_contextual_with_alternate_shape: usize,
    pub named_dependency_missing: usize,
    pub named_dependency_moved: usize,
    pub ordinary_dependency_missing: usize,
    pub ordinary_dependency_moved: usize,
    pub dependency_rebase_underflow: usize,
    pub dependency_shape_rejections: usize,
    pub dependency_budget_rejections: usize,
    pub declaration_collisions: usize,
    pub successful_dependency_probe_visits: usize,
    pub rejected_dependency_probe_visits: usize,
    pub successful_declaration_probe_visits: usize,
    pub rejected_declaration_probe_visits: usize,
    /// Arena entries appended during rebases that subsequently refused.
    /// This excludes temporary-map storage and is not an aggregate byte bound.
    pub failed_rebase_dependency_nodes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermScopeCacheRoute {
    OrdinaryClosed,
    ExactContext,
    NamedClosed,
    PrimaryExact,
    SpareExact,
    PrimaryOutward,
    SpareOutward,
    PrimaryNamedOnly,
    SpareNamedOnly,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TermScopeStopPhase {
    #[default]
    Expression,
    BinderEntry,
    ExactDependency,
    RelativeDependency,
    /// Completed ordinary-output translation, not an input closing request.
    /// Retains the original selected candidate's route/depth observations.
    UniformIndexShiftOutput,
    /// Exact old-to-live named index map; ordinary binder cutoffs still apply.
    NamedIndexProjectionOutput,
    Declaration,
}

/// One first refusal, never an expression, pointer, unbounded trace or retry.
/// The cached hash describes the last CHARGED expression request; it is not
/// the identity of the refusing request and never grants sharing authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermScopeStop {
    pub error: TermScopeError,
    pub phase: TermScopeStopPhase,
    pub charged_visits: usize,
    pub context: usize,
    pub binder_depth: u32,
    /// Expression traversal depth, not the number of active binders.
    pub walk_depth: u32,
    pub ordinary_count: usize,
    pub last_charged_input_hash: Option<u32>,
    pub candidate: Option<TermScopeCacheRoute>,
    pub cached_binder_depth: Option<u32>,
    pub cached_ordinary_count: Option<usize>,
}

/// Opt-in observations of the bounded closing walk, not a full input census.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TermScopeDiagnostics {
    /// Distinct input addresses whose requests consumed a visit, including memo
    /// hits and depth refusals but not requests refused by the visit cap. A
    /// failed walk reports only its observed prefix, never a full input census.
    pub distinct_input_nodes: usize,
    /// Per-kind first-seen address/cached-hash counts, sorted by kind. Cached
    /// hashes never establish structural equality or deferred binder identity.
    pub input_kinds: Vec<TermScopeInputKindCounts>,
    /// Includes the initial empty context even at a zero visit cap; a context
    /// can be entered just before refusal.
    pub distinct_contexts: usize,
    /// Declaration-footprint arena entries retained when the walk stopped;
    /// charged probe work remains in `stats.scope_check_visits`.
    pub declaration_footprint_nodes: usize,
    pub cache: TermScopeCacheDiagnostics,
    pub first_stop: Option<TermScopeStop>,
}

#[derive(Clone, Copy)]
pub(super) struct CandidateShape {
    pub route: Option<TermScopeCacheRoute>,
    pub retained: bool,
    pub alternate: bool,
    pub binder_depth: Option<u32>,
    pub ordinary_count: Option<usize>,
    pub declaration_free_depths: [Option<u32>; 2],
}

#[derive(Clone, Copy)]
pub(super) enum DependencyRejection {
    NamedMissing,
    NamedMoved,
    OrdinaryMissing,
    OrdinaryMoved,
    UnexpectedOrdinary,
    NamedOnlyDepthScreen,
    OrdinaryDepthScreen,
    Underflow,
    Shape,
    Budget,
}

#[derive(Clone, Copy)]
pub(super) enum OutputProjectionObservation {
    Attempt,
    Refusal,
    Hit,
    DependencyVisit,
    OutputVisit,
    OutputMemoHit,
    OutputNodeChanged,
}

type NamedProjectionRootKey = (usize, Vec<(u32, u32)>);

#[derive(Default)]
pub(super) struct Observations {
    inputs: InputCensus,
    named_projection_roots: std::collections::HashMap<NamedProjectionRootKey, Arc<Expr>>,
    cache: TermScopeCacheDiagnostics,
    phase: TermScopeStopPhase,
    last_hash: Option<u32>,
    candidate: Option<TermScopeCacheRoute>,
    cached_depth: Option<u32>,
    cached_ordinary: Option<usize>,
    alternate_shape: bool,
    first_stop: Option<TermScopeStop>,
}

impl Closer<'_> {
    pub(super) fn observe_named_projection_root(
        &mut self,
        output: &Arc<Expr>,
        renaming: &std::collections::HashMap<u32, u32>,
    ) {
        if let Some(observations) = &mut self.observations {
            let mut indices: Vec<_> = renaming.iter().map(|(&old, &new)| (old, new)).collect();
            indices.sort_unstable();
            let key = (Arc::as_ptr(output) as usize, indices);
            match observations.named_projection_roots.entry(key) {
                std::collections::hash_map::Entry::Occupied(_) => {
                    observations.cache.named_projection_repeated_roots += 1;
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(output.clone());
                }
            }
        }
    }

    pub(super) fn observe_phase(&mut self, phase: TermScopeStopPhase) {
        if let Some(observations) = &mut self.observations {
            observations.phase = phase;
            if matches!(
                phase,
                TermScopeStopPhase::Expression | TermScopeStopPhase::BinderEntry
            ) {
                observations.candidate = None;
                observations.cached_depth = None;
                observations.cached_ordinary = None;
                observations.alternate_shape = false;
            }
        }
    }

    pub(super) fn observe_input(&mut self, expression: &Expr) {
        if let Some(observations) = &mut self.observations {
            observations.inputs.observe(self.scope, expression);
            observations.last_hash = Some(expression.hash_cached());
        }
    }

    pub(super) fn observe_route(&mut self, route: TermScopeCacheRoute) {
        if let Some(observations) = &mut self.observations {
            observations.candidate = Some(route);
            let count = match route {
                TermScopeCacheRoute::OrdinaryClosed => &mut observations.cache.ordinary_closed_hits,
                TermScopeCacheRoute::ExactContext => &mut observations.cache.exact_context_hits,
                TermScopeCacheRoute::NamedClosed => &mut observations.cache.named_closed_hits,
                _ => return,
            };
            *count += 1;
        }
    }

    pub(super) fn observe_named_candidate(&mut self) {
        if let Some(observations) = &mut self.observations {
            observations.candidate = Some(TermScopeCacheRoute::NamedClosed);
        }
    }

    pub(super) fn observe_candidate(&mut self, address: usize, expression: &Expr) {
        if self.observations.is_none() {
            return;
        }
        let shape = self
            .contextual
            .observation(address, self.binder_depth, self.ordinary.len());
        let observations = self.observations.as_mut().expect("opt-in observations");
        observations.candidate = shape.route;
        observations.cached_depth = shape.binder_depth;
        observations.cached_ordinary = shape.ordinary_count;
        observations.alternate_shape = shape.alternate;
        let cache = &mut observations.cache;
        match shape.route {
            Some(TermScopeCacheRoute::PrimaryExact) => cache.primary_exact_attempts += 1,
            Some(TermScopeCacheRoute::SpareExact) => cache.spare_exact_attempts += 1,
            Some(TermScopeCacheRoute::PrimaryOutward) => cache.primary_outward_attempts += 1,
            Some(TermScopeCacheRoute::SpareOutward) => cache.spare_outward_attempts += 1,
            Some(_) => unreachable!("contextual selection returns only projection routes"),
            None if shape.retained => {
                cache.contextual_shape_misses += 1;
                if !expression.has_loose_bvars_quick() {
                    cache.shape_misses_without_loose_bvars += 1;
                    let [primary, spare] = shape.declaration_free_depths;
                    cache.declaration_free_primary_shape_misses += usize::from(primary.is_some());
                    cache.declaration_free_spare_shape_misses += usize::from(spare.is_some());
                    let depths = [primary, spare];
                    cache.declaration_free_same_depth_shape_misses += usize::from(
                        depths
                            .iter()
                            .flatten()
                            .any(|depth| *depth == self.binder_depth),
                    );
                    cache.declaration_free_outward_shape_misses += usize::from(
                        depths
                            .iter()
                            .flatten()
                            .any(|depth| *depth > self.binder_depth),
                    );
                    cache.declaration_free_inward_shape_misses += usize::from(
                        depths
                            .iter()
                            .flatten()
                            .any(|depth| *depth < self.binder_depth),
                    );
                }
            }
            None => cache.contextual_absent += 1,
        }
        cache.alternate_shape_available += usize::from(shape.alternate);
    }

    pub(super) fn observe_named_only_candidate(
        &mut self,
        route: TermScopeCacheRoute,
        cached: &super::ContextEntry,
    ) {
        if let Some(observations) = &mut self.observations {
            observations.candidate = Some(route);
            observations.cached_depth = Some(cached.binder_depth);
            observations.cached_ordinary = Some(cached.ordinary_count);
            let count = match route {
                TermScopeCacheRoute::PrimaryNamedOnly => {
                    &mut observations.cache.primary_named_only_attempts
                }
                TermScopeCacheRoute::SpareNamedOnly => {
                    &mut observations.cache.spare_named_only_attempts
                }
                _ => unreachable!("named-only selection reports its actual slot"),
            };
            *count += 1;
        }
    }

    pub(super) fn observe_dependency_node_intern(&mut self, reused: bool) {
        if let Some(observations) = &mut self.observations {
            observations.cache.dependency_node_intern_requests += 1;
            observations.cache.dependency_node_intern_hits += usize::from(reused);
        }
    }

    pub(super) fn observe_named_prefix_proof(&mut self) {
        if let Some(observations) = &mut self.observations {
            observations.cache.named_prefix_proofs += 1;
        }
    }

    pub(super) fn observe_composed_shift(&mut self, reused: bool) {
        if let Some(observations) = &mut self.observations {
            observations.cache.uniform_shift_composed_inputs += 1;
            observations.cache.uniform_shift_composed_cache_hits += usize::from(reused);
        }
    }

    pub(super) fn observe_output_node_intern(&mut self, reused: bool) {
        if let Some(observations) = &mut self.observations {
            observations.cache.output_node_intern_requests += 1;
            observations.cache.output_node_intern_hits += usize::from(reused);
        }
    }

    pub(super) fn observe_uniform_shift(&mut self, event: OutputProjectionObservation) {
        if let Some(observations) = &mut self.observations {
            let cache = &mut observations.cache;
            let count = match event {
                OutputProjectionObservation::Attempt => &mut cache.uniform_shift_attempts,
                OutputProjectionObservation::Refusal => &mut cache.uniform_shift_refusals,
                OutputProjectionObservation::Hit => &mut cache.uniform_shift_contextual_hits,
                OutputProjectionObservation::DependencyVisit => {
                    &mut cache.uniform_shift_dependency_visits
                }
                OutputProjectionObservation::OutputVisit => &mut cache.uniform_shift_output_visits,
                OutputProjectionObservation::OutputMemoHit => {
                    &mut cache.uniform_shift_output_memo_hits
                }
                OutputProjectionObservation::OutputNodeChanged => {
                    &mut cache.uniform_shift_output_changed_nodes
                }
            };
            *count += 1;
        }
    }

    pub(super) fn observe_named_projection(&mut self, event: OutputProjectionObservation) {
        if let Some(observations) = &mut self.observations {
            let cache = &mut observations.cache;
            let count = match event {
                OutputProjectionObservation::Attempt => &mut cache.named_projection_attempts,
                OutputProjectionObservation::Refusal => &mut cache.named_projection_refusals,
                OutputProjectionObservation::Hit => &mut cache.named_projection_contextual_hits,
                OutputProjectionObservation::DependencyVisit => {
                    &mut cache.named_projection_dependency_visits
                }
                OutputProjectionObservation::OutputVisit => {
                    &mut cache.named_projection_output_visits
                }
                OutputProjectionObservation::OutputMemoHit => {
                    &mut cache.named_projection_output_memo_hits
                }
                OutputProjectionObservation::OutputNodeChanged => {
                    &mut cache.named_projection_output_changed_nodes
                }
            };
            *count += 1;
        }
    }

    pub(super) fn observe_contextual_hit(&mut self, named_only: bool) {
        if let Some(observations) = &mut self.observations {
            observations.cache.contextual_hits += 1;
            observations.cache.named_only_contextual_hits += usize::from(named_only);
        }
    }

    pub(super) fn observe_contextual_rejection(&mut self) {
        if let Some(observations) = &mut self.observations {
            observations.cache.rejected_contextual_with_alternate_shape +=
                usize::from(observations.alternate_shape);
        }
    }

    pub(super) fn observe_dependency_rejection(&mut self, reason: DependencyRejection) {
        if let Some(observations) = &mut self.observations {
            let cache = &mut observations.cache;
            let count = match reason {
                DependencyRejection::NamedMissing => &mut cache.named_dependency_missing,
                DependencyRejection::NamedMoved => &mut cache.named_dependency_moved,
                DependencyRejection::OrdinaryMissing => &mut cache.ordinary_dependency_missing,
                DependencyRejection::OrdinaryMoved => &mut cache.ordinary_dependency_moved,
                DependencyRejection::UnexpectedOrdinary => {
                    &mut cache.named_only_ordinary_rejections
                }
                DependencyRejection::NamedOnlyDepthScreen => {
                    &mut cache.named_only_depth_screen_rejections
                }
                DependencyRejection::OrdinaryDepthScreen => {
                    &mut cache.ordinary_depth_screen_rejections
                }
                DependencyRejection::Underflow => &mut cache.dependency_rebase_underflow,
                DependencyRejection::Shape => &mut cache.dependency_shape_rejections,
                DependencyRejection::Budget => &mut cache.dependency_budget_rejections,
            };
            *count += 1;
        }
    }

    pub(super) fn observe_probe_result(
        &mut self,
        dependency: bool,
        success: bool,
        visits: usize,
        nodes: usize,
    ) {
        if let Some(observations) = &mut self.observations {
            let cache = &mut observations.cache;
            let count = match (dependency, success) {
                (true, true) => &mut cache.successful_dependency_probe_visits,
                (true, false) => &mut cache.rejected_dependency_probe_visits,
                (false, true) => &mut cache.successful_declaration_probe_visits,
                (false, false) => &mut cache.rejected_declaration_probe_visits,
            };
            *count += visits;
            if !success {
                cache.failed_rebase_dependency_nodes += nodes;
            }
        }
    }

    pub(super) fn observe_declaration_collision(&mut self) {
        if let Some(observations) = &mut self.observations {
            observations.cache.declaration_collisions += 1;
        }
    }

    pub(super) fn observe_stop(&mut self, error: &TermScopeError) {
        if let Some(observations) = &mut self.observations
            && observations.first_stop.is_none()
        {
            observations.first_stop = Some(TermScopeStop {
                error: error.clone(),
                phase: observations.phase,
                charged_visits: self.stats.visits,
                context: self.context,
                binder_depth: self.binder_depth,
                walk_depth: self.walk_depth,
                ordinary_count: self.ordinary.len(),
                last_charged_input_hash: observations.last_hash,
                candidate: observations.candidate,
                cached_binder_depth: observations.cached_depth,
                cached_ordinary_count: observations.cached_ordinary,
            });
        }
    }

    pub(super) fn diagnostic_report(&self) -> TermScopeDiagnostics {
        TermScopeDiagnostics {
            distinct_input_nodes: self.observations.as_ref().map_or(0, |o| o.inputs.len()),
            input_kinds: self
                .observations
                .as_ref()
                .map_or_else(Vec::new, |o| o.inputs.counts()),
            distinct_contexts: self.contexts.len() + 1,
            declaration_footprint_nodes: self.footprints.len(),
            cache: self
                .observations
                .as_ref()
                .map_or_else(TermScopeCacheDiagnostics::default, |o| o.cache),
            first_stop: self
                .observations
                .as_ref()
                .and_then(|o| o.first_stop.clone()),
        }
    }
}
