///! `Inc` implementations for common foreign types

use super::{Inc, ShallowEval};

impl<
    InnerSource,
    Source: ShallowEval<Output = Option<InnerSource>>,
    Output: Inc<InnerSource>,
> Inc<Source> for Option<Output> {
    fn fresh_eval(source: Source) -> Self {
        source.shallow_eval().map(Output::fresh_eval)
    }

    fn re_eval(&mut self, source: Source) {
        match source.shallow_eval() {
            Some(inner) => {
                match self {
                    &mut Some(ref mut prev) => {
                        prev.re_eval(inner);
                    }
                    &mut None => {
                        *self = Some(Output::fresh_eval(inner));
                    }
                }
            }
            None => {
                *self = None;
            }
        }
    }
}

#[test]
fn test_option() {
    use std::ops::Deref;
    use super::{Raw, Cache, CountEvaluations};

    #[derive(PartialEq, Clone, Copy, Debug)]
    struct ThreeHalvesPower(f64);

    #[derive(PartialEq, Clone, Copy, Debug)]
    struct Cube(f64);

    impl ShallowEval for ThreeHalvesPower {
        type Output = Option<Cube>;

        fn shallow_eval(self) -> Self::Output {
            if self.0 >= 0.0 {
                Some(Cube(self.0.sqrt()))
            } else {
                None
            }
        }
    }

    impl ShallowEval for Cube {
        type Output = f64;

        fn shallow_eval(self) -> Self::Output {
            self.0 * self.0 * self.0
        }
    }

    let mut three_halves: Option<Cache<Cube, CountEvaluations<Raw<f64>>>> =
        Inc::fresh_eval(ThreeHalvesPower(4.0));
    assert_eq!(three_halves.unwrap().deref().output, 8.0);
    assert_eq!(three_halves.unwrap().num_evaluations, 1);

    three_halves.re_eval(ThreeHalvesPower(4.0));
    assert_eq!(three_halves.unwrap().deref().output, 8.0);
    assert_eq!(three_halves.unwrap().num_evaluations, 1);

    three_halves.re_eval(ThreeHalvesPower(9.0));
    assert_eq!(three_halves.unwrap().deref().output, 27.0);
    assert_eq!(three_halves.unwrap().num_evaluations, 2);

    three_halves.re_eval(ThreeHalvesPower(-4.0));
    assert!(three_halves.is_none());

    three_halves.re_eval(ThreeHalvesPower(9.0));
    assert_eq!(three_halves.unwrap().deref().output, 27.0);
}

impl<Source, Output: Inc<Source>> Inc<Source> for Box<Output> {
    fn fresh_eval(source: Source) -> Self {
        Box::new(Output::fresh_eval(source))
    }

    fn re_eval(&mut self, source: Source) {
        (**self).re_eval(source)
    }
}
