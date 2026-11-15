// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn synthetic<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text(&function.name, &mut self.name)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::SyntheticSymbolName {
            function: function.id.index(),
            name: take(&mut self.name),
        });
        Ok(())
    }
    pub(super) fn duplicate<O: ExecutionObserver>(
        &mut self,
        first: &Function,
        second: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.ready(work)?;
        work.text(&second.name, &mut self.name)?;
        work.producer(&first.producer, &mut self.first_producer)?;
        work.producer(&second.producer, &mut self.second_producer)?;
        work.path(&first.display_path, &mut self.first_path)?;
        work.path(&second.display_path, &mut self.second_path)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>())?;
        self.errors.push(ValidationError::DuplicateFunctionSymbol {
            name: take(&mut self.name),
            first: first.id.index(),
            second: second.id.index(),
            first_producer: self.first_producer.take(),
            second_producer: self.second_producer.take(),
            first_display_path: self.first_path.take(),
            second_display_path: self.second_path.take(),
        });
        Ok(())
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn producer(
        &mut self,
        source: &Option<Producer>,
        output: &mut Option<Producer>,
    ) -> R {
        self.admit(2, size_of::<Option<Producer>>())?;
        if output.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        match source {
            None => {}
            Some(producer) => {
                self.admit(6, size_of::<Producer>())?;
                // Exhaustive source inventory; never use a derived clone of
                // the variable Other string. Own its header before copying.
                *output = Some(match producer {
                    Producer::TRust => Producer::TRust,
                    Producer::Clean => Producer::Clean,
                    Producer::TrustIr => Producer::TrustIr,
                    Producer::TSwift => Producer::TSwift,
                    Producer::TC => Producer::TC,
                    Producer::Other(_) => Producer::Other(String::new()),
                });
                if let Producer::Other(text) = producer {
                    match output.as_mut() {
                        Some(Producer::Other(owned)) => self.text(text, owned)?,
                        _ => return Err(ObservedValueError::InvalidRange),
                    }
                }
            }
        }
        Ok(())
    }
    pub(super) fn path(&mut self, source: &Option<String>, output: &mut Option<String>) -> R {
        self.admit(2, size_of::<Option<String>>())?;
        if output.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        match source {
            None => {}
            Some(path) => {
                *output = Some(String::new());
                match output.as_mut() {
                    Some(owned) => self.text(path, owned)?,
                    None => return Err(ObservedValueError::InvalidRange),
                }
            }
        }
        Ok(())
    }
}
