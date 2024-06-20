use prusti_contracts::*;

// From Kassios and Müller (2010) (simplified)

#[requires(f |= || -> i32 [ requires(true), ensures(cl_result >= 2) ])]
fn foo<T: FnMut() -> i32>(f: T) {}

fn main() {
    let mut x = 0;
    let mut inc = closure!(
        #[view(x: i32)]
        #[invariant(*views.x >= 0)]
        #[invariant(old(*views.x) <= *views.x)]
        #[requires(true)]
        #[ensures(old(*views.x) + 1 == *views.x)]
        #[ensures(result == old(*views.x))]
        || -> i32 { let r = x; x += 1; r }
    );

    inc();
    inc();
    foo(inc);
}
