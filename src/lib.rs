use std::ops::Deref;
use std::cmp::Ordering;

/// A value which can be "incrementally" re-computed as its inputs change.
///
/// A type implementing `Inc` represents a result that can be evaluated from a `Source` type, and
/// which can be evaluated *more efficiently* if the result of a previous evaluation on a similar
/// input is available.  Because this incremental re-evaluation feature exists purely for
/// performance purposes, its use should not affect the semantics of the evaluation.
pub trait Inc<Source> {
    /// Evaluate a given input.
    ///
    /// This method computes its result "from scratch," without considering any previous input,
    /// so it may be less efficient than `re_eval`.
    fn fresh_eval(source: Source) -> Self;

    /// Evaluate a given input incrementally, reusing the result of a previous evaluation.
    ///
    /// This method may be more efficient than `fresh_eval` when the previous result was generated
    /// from an input similar to the current input.
    ///
    /// # Implementation notes
    ///
    /// `re_eval` should always set `self` to exactly the same value as `fresh_eval` would produce
    /// for a given input. In other words, the following two statements should always be
    /// semantically equivalent:
    ///
    /// ```ignore
    /// output.re_eval(source);
    /// ```
    ///
    /// ```ignore
    /// *output = Inc::fresh_eval(source);
    /// ```
    fn re_eval(&mut self, source: Source);
}

/// A value which can be evaluated to a result which may contain un-evaluated parts.
///
/// The exact meaning of "un-evaluated" here is subjective, but roughly speaking it means that parts
/// of the output may be suitable for use as inputs to further evaluations.  For example, a
/// numerical expression tree which supports shallow evaluation may evaluate to a simpler numerical
/// expression tree, so that `5^2` may evaluate to `5 * 5`, but not complete the full evaluation to
/// `25`.
///
/// This type is useful for *incremental* evaluation, because it allows us to recognize when two
/// inputs produce overlapping sub-computations, even when the inputs are not identical.  If the
/// inputs did not support shallow evaluation, their internal computation steps would be opaque, and
/// it would be impossible to tell if they overlapped or not.  Shallow evaluation allows the
/// internal steps of an evaluation to be visible, which in turns makes them optimizable.
pub trait ShallowEval {
    /// A partially-evaluated result, which may contain conceptually "un-evaluated" parts.
    type Output;

    /// Evaluate this input, producing an output which may contain conceptually "un-evaluated" parts.
    fn shallow_eval(self) -> Self::Output;
}

/// A wrapper type for testing and debugging evaluation strategies, which increments a counter
/// every time it is evaluated.
pub struct CountEvaluations<T> {
    pub num_evaluations: u32,
    pub content: T,
}

impl<Source, T: Inc<Source>> Inc<Source> for CountEvaluations<T> {
    fn fresh_eval(source: Source) -> Self {
        CountEvaluations {
            num_evaluations: 1,
            content: T::fresh_eval(source),
        }
    }

    fn re_eval(&mut self, source: Source) {
        self.num_evaluations += 1;
        self.content.re_eval(source);
    }
}

impl<T> Deref for CountEvaluations<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.content
    }
}

/// A value with the simplest possible evaluation strategy: *always recompute from scratch.*
///
/// This type is intended to be wrapped in types like `Cache` which implement smarter incremental
/// evaluation strategies.  Even though a `Raw` value will always recompute from scratch, wrapper
/// types like `Cache` may intelligently preempt that computation before it ever happens.
///
/// Abstractly, `Raw` types are meant to represent the "leaves" or "atoms" of incremental evaluation
/// trees; they are results so small that they should not (or cannot) support intelligent caching or
/// diffing of their sub-components.  This is why `Raw` stores the direct result of "shallowly"
/// evaluating an input: `Raw` is used for units of computation so small that "shallow" evaluation
/// becomes the same as ordinary, full evaluation.
///
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use incremental::{Inc, ShallowEval, Raw};
///
/// struct SquareOp(i32);
///
/// impl ShallowEval for SquareOp {
///     type Output = i32;
///
///     fn shallow_eval(self) -> i32 {
///         let SquareOp(x) = self;
///         x * x
///     }
/// }
///
/// let mut squ: Raw<i32> = Inc::fresh_eval(SquareOp(2));
/// assert_eq!(squ.output, 4);
///
/// squ.re_eval(SquareOp(3));
/// assert_eq!(squ.output, 9);
/// ```
///
/// `Raw` always recomputes, even for identical inputs:
///
/// ```
/// #   use incremental::{Inc, ShallowEval, Raw};
/// #
/// #   struct SquareOp(i32);
/// #
/// #   impl ShallowEval for SquareOp {
/// #       type Output = i32;
/// #
/// #       fn shallow_eval(self) -> i32 {
/// #           let SquareOp(x) = self;
/// #           x * x
/// #       }
/// #   }
/// use incremental::CountEvaluations;
///
/// let mut squ: CountEvaluations<Raw<i32>> = Inc::fresh_eval(SquareOp(2));
/// assert_eq!(squ.output, 4);
/// assert_eq!(squ.num_evaluations, 1);
///
/// squ.re_eval(SquareOp(3));
/// assert_eq!(squ.output, 9);
/// assert_eq!(squ.num_evaluations, 2);
///
/// squ.re_eval(SquareOp(3));
/// assert_eq!(squ.output, 9);
/// assert_eq!(squ.num_evaluations, 3); // always recomputes, even for identical inputs
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Raw<Output> {
    pub output: Output,
}

impl<Output, Source: ShallowEval<Output = Output>> Inc<Source> for Raw<Output> {
    fn fresh_eval(source: Source) -> Self {
        Raw { output: source.shallow_eval() }
    }

    fn re_eval(&mut self, source: Source) {
        self.output = source.shallow_eval();
    }
}

/// A value which avoids recomputing itself for identical consecutive inputs.
///
/// If two consecutive inputs are not exactly equal, this type will recompute itself using its
/// contents' evaluation strategy.
///
/// You can use this type to introduce caching logic at any level of a structure of nested
/// incrementally computable values.
///
/// # Examples:
///
/// Basic usage:
///
/// ```
/// use incremental::{Inc, ShallowEval, Raw, Cache};
///
/// #[derive(Clone, PartialEq)]
/// struct SquareOp(i32);
///
/// impl ShallowEval for SquareOp {
///     type Output = i32;
///
///     fn shallow_eval(self) -> i32 {
///         let SquareOp(x) = self;
///         x * x
///     }
/// }
///
/// let mut squ: Cache<SquareOp, Raw<i32>> = Inc::fresh_eval(SquareOp(2));
/// assert_eq!(squ.output, 4);
///
/// squ.re_eval(SquareOp(5));
/// assert_eq!(squ.output, 25);
/// ```
///
/// `Cache` avoids recomputing itself when evaluated with identical consecutive inputs:
///
/// ```
/// #   use incremental::{Inc, ShallowEval, Raw, Cache};
/// #   #[derive(Clone, PartialEq)]
/// #   struct SquareOp(i32);
/// #
/// #   impl ShallowEval for SquareOp {
/// #       type Output = i32;
/// #
/// #       fn shallow_eval(self) -> i32 {
/// #           let SquareOp(x) = self;
/// #           x * x
/// #       }
/// #   }
/// use incremental::CountEvaluations;
///
/// let mut squ: Cache<SquareOp, CountEvaluations<Raw<i32>>> = Inc::fresh_eval(SquareOp(2));
/// assert_eq!(squ.output, 4);
/// assert_eq!(squ.num_evaluations, 1);
///
/// squ.re_eval(SquareOp(5));
/// assert_eq!(squ.output, 25);
/// assert_eq!(squ.num_evaluations, 2);
///
/// squ.re_eval(SquareOp(5));
/// assert_eq!(squ.output, 25);
/// assert_eq!(squ.num_evaluations, 2); // does not recompute for identical inputs
///
/// squ.re_eval(SquareOp(2));
/// assert_eq!(squ.output, 4);
/// assert_eq!(squ.num_evaluations, 3); // does not remember anything except the previous input
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Cache<Source, Output> {
    source: Source,
    output: Output,
}

impl<Source, Output> Deref for Cache<Source, Output> {
    type Target = Output;

    fn deref(&self) -> &Self::Target {
        &self.output
    }
}

impl<Source: Clone + PartialEq, Output: Inc<Source>> Inc<Source> for Cache<Source, Output> {
    fn fresh_eval(source: Source) -> Self {
        Cache {
            source: source.clone(),
            output: Output::fresh_eval(source),
        }
    }

    fn re_eval(&mut self, source: Source) {
        if self.source != source {
            self.source = source.clone();
            self.output.re_eval(source);
        }
    }
}

impl<Source, Output: PartialEq> PartialEq for Cache<Source, Output> {
    /// Equality on `Cache`s compares only their outputs, not their cached inputs, because their
    /// cached inputs should have no semantically observable effects.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental::{Inc, ShallowEval, Raw, Cache};
    ///
    /// #[derive(Clone, PartialEq, Debug)]
    /// struct SquareOp(i32);
    ///
    /// impl ShallowEval for SquareOp {
    ///     type Output = i32;
    ///
    ///     fn shallow_eval(self) -> i32 {
    ///         let SquareOp(x) = self;
    ///         x * x
    ///     }
    /// }
    ///
    /// let mut squ1: Cache<SquareOp, Raw<i32>> = Inc::fresh_eval(SquareOp(2));
    /// let mut squ2: Cache<SquareOp, Raw<i32>> = Inc::fresh_eval(SquareOp(-2));
    /// assert_eq!(squ1.output, 4);
    /// assert_eq!(squ2.output, 4);
    /// assert_eq!(squ1, squ2);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.output == other.output
    }
}

impl<Source, Output: Eq> Eq for Cache<Source, Output> {}

impl<Source, Output: PartialOrd> PartialOrd for Cache<Source, Output> {
    /// Ordering on `Cache`s compares only their outputs, not their cached inputs, because their
    /// cached inputs have no semantically observable effects.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.output.partial_cmp(&other.output)
    }

    fn lt(&self, other: &Self) -> bool {
        self.output < other.output
    }

    fn le(&self, other: &Self) -> bool {
        self.output <= other.output
    }

    fn gt(&self, other: &Self) -> bool {
        self.output > other.output
    }

    fn ge(&self, other: &Self) -> bool {
        self.output >= other.output
    }
}

impl<Source, Output: Ord> Ord for Cache<Source, Output> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.output.cmp(&other.output)
    }
}
