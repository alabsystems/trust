pub struct Id(pub u32);
impl Id {
    pub fn next(&self) -> Option<Id> {
        self.0.checked_add(1).map(Id)
    }
}
