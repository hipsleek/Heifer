use prusti_contracts::*;

#[ensures(result >= 3)]
fn test() -> i32 {
  let mut x = 0;
  let mut b = closure!(
    #[view(x: i32)]
    #[invariant(*views.x >= 0)]
    #[invariant(old(*views.x) <= *views.x)]
    #[ensures(old(*views.x) + 1 == *views.x)]
    #[ensures(result == old(*views.x) + 1)]
    || -> i32 { x = x + 1; x }
  );
  let mut y = 0;
  let mut c = closure!(
    #[view(y: i32)]
    #[invariant(*views.y >= 0)]
    #[invariant(old(*views.y) <= *views.y)]
    #[ensures(old(*views.y) + 2 == *views.y)]
    #[ensures(result == old(*views.y) + 2)]
    || -> i32 { y = y + 2; y }
  );
  b() + c()
}

fn main() {}