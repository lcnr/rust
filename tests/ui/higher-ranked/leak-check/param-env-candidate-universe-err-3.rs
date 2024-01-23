// check-pass

// Regression tests discovered while working on #119820.
// This pattern was found via crater in macro-generated code.
trait Deserialize<'de> {
    fn deserialize() -> Self;
}

trait DeserializeOwned: for<'de> Deserialize<'de> {}
impl<T: for<'de> Deserialize<'de>> DeserializeOwned for T {}
impl<'de> Deserialize<'de> for bool {
    fn deserialize() -> Self {
        true
    }
}

struct ContainsBoolAndWrapper {
    b: bool,
    w: NeedsOwned,
}
struct NeedsOwned(bool);

impl<'de> Deserialize<'de> for NeedsOwned
where
    bool: DeserializeOwned,
{
    fn deserialize() -> Self {
        NeedsOwned(<bool as Deserialize>::deserialize())
    }
}

impl<'de> Deserialize<'de> for ContainsBoolAndWrapper
where
    bool: Deserialize<'de>,
{
    fn deserialize() -> Self {
        ContainsBoolAndWrapper {
            b: <bool as Deserialize>::deserialize(),
            w: <NeedsOwned as Deserialize>::deserialize(),
        }
    }
}

fn main() {}
