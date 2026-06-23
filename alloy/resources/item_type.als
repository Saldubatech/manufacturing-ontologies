module resources/item_type

// Placeholder ItemType for the relocated kanban spike. Kept local to `resources`
// so the spike stays decoupled from the redesigned `reference_data/item` (the real
// Item entity). The kanban redesign (DT-001.08) will repoint cards at reference_data.
abstract sig ItemType {}
