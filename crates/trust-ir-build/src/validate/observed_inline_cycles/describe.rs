// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use graph::nominal;
impl State<'_> {
    pub(super) fn describe_cycles<O: ExecutionObserver>(
        &mut self,
        m: &Module,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut i = 0;
        loop {
            w.admit(1, size_of::<Option<&Vec<usize>>>())?;
            let Some(length) = self.cycles.get(i).map(Vec::len) else {
                break;
            };
            let mut j = 0;
            while j < length {
                w.admit(4, size_of::<usize>() + size_of::<Node>())?;
                let index = *self
                    .cycles
                    .get(i)
                    .and_then(|c| c.get(j))
                    .ok_or(ObservedValueError::InvalidRange)?;
                let node = *self
                    .nodes
                    .get(index)
                    .ok_or(ObservedValueError::InvalidRange)?;
                if j == 1 {
                    w.text(" (cycle through ", &mut self.text)?;
                } else if j > 1 {
                    w.text(", ", &mut self.text)?;
                }
                self.describe_node(m, node, w)?;
                w.next(&mut j)?;
            }
            w.admit(1, 0)?;
            if length > 1 {
                w.text(")", &mut self.text)?;
            }
            w.reserve(&mut self.errors)?;
            w.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
            self.errors.push(ValidationError::InlineAggregateCycle {
                ty: take(&mut self.text),
            });
            w.next(&mut i)?;
        }
        Ok(())
    }
    fn describe_node<O: ExecutionObserver>(
        &mut self,
        m: &Module,
        node: Node,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(5, size_of::<Option<&str>>())?;
        let (kind, id, name) = match node {
            Node::Struct(id) => (
                "struct",
                id,
                nominal(&m.structs, id, |d| d.id.index(), w)?.map(|d| d.name.as_str()),
            ),
            Node::Enum(id) => (
                "enum",
                id,
                nominal(&m.enums, id, |d| d.id.index(), w)?.map(|d| d.name.as_str()),
            ),
            Node::Record(id) => (
                "record",
                id,
                nominal(&m.records, id, |d| d.id.index(), w)?.map(|d| d.name.as_str()),
            ),
            Node::Closure(id) => ("closure type", id, None),
            Node::Row(id) => ("type", id, None),
        };
        w.text(kind, &mut self.text)?;
        w.text(" #", &mut self.text)?;
        w.unsigned(u128::from(id), &mut self.text)?;
        if let Some(name) = name {
            // Original formatting encloses raw names in apostrophes. It does
            // not debug-escape, trim or normalize their contents.
            w.text(" '", &mut self.text)?;
            w.text(name, &mut self.text)?;
            w.text("'", &mut self.text)?;
        }
        if let Node::Row(id) = node
            && let Some(ty) = w.at(&m.types, id as usize)?
        {
            w.admit(1, size_of::<String>())?;
            self.render = ty.display_observed(w.session, w.site)?;
            w.text(" (", &mut self.text)?;
            w.text(&self.render, &mut self.text)?;
            w.flat(take(&mut self.render));
            w.admit(1, 0)?;
            w.text(")", &mut self.text)?;
        }
        Ok(())
    }
}
