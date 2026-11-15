// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> Children<'a> {
    fn next<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R<Option<Item<'a>>> {
        work.admit(8, size_of::<Option<Item<'a>>>() + size_of::<usize>())?;
        let index = self.index;
        let (ty, field) = match self.types {
            ChildTypes::Repeated(ty) => (ty, None),
            ChildTypes::Positional(types) => {
                let Some(ty) = work.at(types, index)? else {
                    return Ok(None);
                };
                (ty, None)
            }
            ChildTypes::Fields(fields) => {
                let Some(field) = work.at(fields, index)? else {
                    return Ok(None);
                };
                (&field.ty, Some(field.name.as_str()))
            }
        };
        work.admit(1, size_of::<ConstantChildren<'a>>())?;
        let Some(constant) = self.constants.next() else {
            return Ok(None);
        };
        work.next(&mut self.index)?;
        let wrong_name = if let Some(names) = self.names {
            let actual = work
                .at(names, index)?
                .ok_or(ObservedValueError::InvalidRange)?
                .0
                .as_str();
            let expected = field.ok_or(ObservedValueError::InvalidRange)?;
            (!work.equal(actual, expected)?).then_some((actual, expected, index))
        } else {
            None
        };
        work.admit(2, size_of::<Option<PathElement<'a>>>())?;
        let path = if self.names.is_some() {
            field.map(PathElement::Field)
        } else {
            self.indexed.then_some(PathElement::Index(index))
        };
        Ok(Some(Item {
            constant,
            ty,
            path,
            wrong_name,
        }))
    }
}
impl<'a> State<'a> {
    pub(super) fn run<'m: 'a, O: ExecutionObserver>(
        &mut self,
        symbols: &ObservedConstantSymbols<'_, 'm>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.uniform = Some(
            self.root
                .uniform_element_lists_observed(work.session, work.site)?,
        );
        loop {
            work.admit(1, size_of::<Item<'a>>())?;
            let item = self.current.ok_or(ObservedValueError::InvalidRange)?;
            if let Some(path) = item.path {
                work.reserve(&mut self.path)?;
                work.admit(1, size_of::<PathElement<'a>>())?;
                self.path.push(path);
            }
            self.retire_discriminants(work);
            self.retire_layout(work);
            work.admit(1, 0)?;
            self.children = if let Some((actual, expected, index)) = item.wrong_name {
                work.text("field '", &mut self.expected)?;
                work.text(expected, &mut self.expected)?;
                work.text("'", &mut self.expected)?;
                work.text("field '", &mut self.actual)?;
                work.text(actual, &mut self.actual)?;
                work.text("' at index ", &mut self.actual)?;
                work.unsigned(index as u128, &mut self.actual)?;
                self.mismatch_ready(work)?;
                None
            } else {
                self.node(symbols, item, work)?
            };
            work.admit(1, size_of::<Option<Item<'a>>>())?;
            let first = match self.children.as_mut() {
                Some(children) => children.next(work)?,
                None => None,
            };
            if let Some(first) = first {
                work.admit(1, size_of::<usize>())?;
                if self
                    .children
                    .as_ref()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .constants
                    .len()
                    != 0
                {
                    work.reserve(&mut self.pending)?;
                    work.admit(1, size_of::<(Children<'a>, usize)>())?;
                    self.pending.push((
                        self.children
                            .take()
                            .ok_or(ObservedValueError::InvalidRange)?,
                        self.path.len(),
                    ));
                } else {
                    work.fixed(self.children.take());
                }
                self.current = Some(first);
                continue;
            }
            work.fixed(self.children.take());
            loop {
                work.admit(1, size_of::<Option<&mut (Children<'a>, usize)>>())?;
                let Some((children, depth)) = self.pending.last_mut() else {
                    return Ok(());
                };
                loop {
                    work.admit(1, size_of::<usize>())?;
                    if self.path.len() <= *depth {
                        break;
                    }
                    work.admit(1, size_of::<Option<PathElement<'a>>>())?;
                    self.path.pop();
                }
                if let Some(next) = children.next(work)? {
                    self.current = Some(next);
                    break;
                }
                work.admit(1, size_of::<Option<(Children<'a>, usize)>>())?;
                work.fixed(self.pending.pop());
            }
        }
    }
}
