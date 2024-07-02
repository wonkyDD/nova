use crate::{
    ecmascript::types::{OrdinaryObject, Value},
    heap::{CompactionLists, HeapMarkAndSweep, WorkQueues},
};

#[derive(Debug, Clone)]
pub struct WeakRefHeapData {
    pub(crate) object_index: Option<OrdinaryObject>,
    pub(crate) value: Value,
    pub(crate) is_strong: bool,
}

impl Default for WeakRefHeapData {
    fn default() -> Self {
        Self {
            object_index: None,
            value: Value::Undefined,
            is_strong: false,
        }
    }
}

impl HeapMarkAndSweep for WeakRefHeapData {
    fn mark_values(&self, queues: &mut WorkQueues) {
        self.object_index.mark_values(queues);
        if self.is_strong {
            self.object_index.mark_values(queues);
        }
    }

    fn sweep_values(&mut self, compactions: &CompactionLists) {
        self.object_index.sweep_values(compactions);
        self.value.sweep_values(compactions);
        self.is_strong = false;
    }
}
