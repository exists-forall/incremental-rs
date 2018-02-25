use super::{Inc, ShallowEval};

/// Incremental evaluation of tuples, from sources which can be shallowly evaluated into two
/// sources, one for each component.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use incremental::{Inc, Raw, ShallowEval};
///
/// struct PowsOp(i32);
/// struct SquareOp(i32);
/// struct CubeOp(i32);
///
/// impl ShallowEval for PowsOp {
///     type Output = (SquareOp, CubeOp);
///
///     fn shallow_eval(self) -> Self::Output {
///         let PowsOp(x) = self;
///         (SquareOp(x), CubeOp(x))
///     }
/// }
///
/// impl ShallowEval for SquareOp {
///     type Output = i32;
///
///     fn shallow_eval(self) -> Self::Output {
///         let SquareOp(x) = self;
///         x * x
///     }
/// }
///
/// impl ShallowEval for CubeOp {
///     type Output = i32;
///
///     fn shallow_eval(self) -> Self::Output {
///         let CubeOp(x) = self;
///         x * x * x
///     }
/// }
///
/// let mut pows: (Raw<i32>, Raw<i32>) = Inc::fresh_eval(PowsOp(2));
/// assert_eq!(pows.0.output, 4);
/// assert_eq!(pows.1.output, 8);
///
/// pows.re_eval(PowsOp(5));
/// assert_eq!(pows.0.output, 25);
/// assert_eq!(pows.1.output, 125);
/// ```
impl<
    ASource,
    BSource,
    Source: ShallowEval<Output = (ASource, BSource)>,
    A: Inc<ASource>,
    B: Inc<BSource>,
> Inc<Source> for (A, B) {
    fn fresh_eval(source: Source) -> Self {
        let (a_source, b_source) = source.shallow_eval();
        (A::fresh_eval(a_source), B::fresh_eval(b_source))
    }

    fn re_eval(&mut self, source: Source) {
        let (a_source, b_source) = source.shallow_eval();
        self.0.re_eval(a_source);
        self.1.re_eval(b_source);
    }
}

impl<
    ASource,
    BSource,
    CSource,
    Source: ShallowEval<Output = (ASource, BSource, CSource)>,
    A: Inc<ASource>,
    B: Inc<BSource>,
    C: Inc<CSource>,
> Inc<Source> for (A, B, C) {
    fn fresh_eval(source: Source) -> Self {
        let (a_source, b_source, c_source) = source.shallow_eval();
        (
            A::fresh_eval(a_source),
            B::fresh_eval(b_source),
            C::fresh_eval(c_source),
        )
    }

    fn re_eval(&mut self, source: Source) {
        let (a_source, b_source, c_source) = source.shallow_eval();
        self.0.re_eval(a_source);
        self.1.re_eval(b_source);
        self.2.re_eval(c_source);
    }
}

impl<
    ASource,
    BSource,
    CSource,
    DSource,
    Source: ShallowEval<Output = (ASource, BSource, CSource, DSource)>,
    A: Inc<ASource>,
    B: Inc<BSource>,
    C: Inc<CSource>,
    D: Inc<DSource>,
> Inc<Source> for (A, B, C, D) {
    fn fresh_eval(source: Source) -> Self {
        let (a_source, b_source, c_source, d_source) = source.shallow_eval();
        (
            A::fresh_eval(a_source),
            B::fresh_eval(b_source),
            C::fresh_eval(c_source),
            D::fresh_eval(d_source),
        )
    }

    fn re_eval(&mut self, source: Source) {
        let (a_source, b_source, c_source, d_source) = source.shallow_eval();
        self.0.re_eval(a_source);
        self.1.re_eval(b_source);
        self.2.re_eval(c_source);
        self.3.re_eval(d_source);
    }
}

impl<
    ASource,
    BSource,
    CSource,
    DSource,
    ESource,
    Source: ShallowEval<Output = (ASource, BSource, CSource, DSource, ESource)>,
    A: Inc<ASource>,
    B: Inc<BSource>,
    C: Inc<CSource>,
    D: Inc<DSource>,
    E: Inc<ESource>,
> Inc<Source> for (A, B, C, D, E) {
    fn fresh_eval(source: Source) -> Self {
        let (a_source, b_source, c_source, d_source, e_source) = source.shallow_eval();
        (
            A::fresh_eval(a_source),
            B::fresh_eval(b_source),
            C::fresh_eval(c_source),
            D::fresh_eval(d_source),
            E::fresh_eval(e_source),
        )
    }

    fn re_eval(&mut self, source: Source) {
        let (a_source, b_source, c_source, d_source, e_source) = source.shallow_eval();
        self.0.re_eval(a_source);
        self.1.re_eval(b_source);
        self.2.re_eval(c_source);
        self.3.re_eval(d_source);
        self.4.re_eval(e_source);
    }
}

impl<
    ASource,
    BSource,
    CSource,
    DSource,
    ESource,
    FSource,
    Source: ShallowEval<Output = (ASource, BSource, CSource, DSource, ESource, FSource)>,
    A: Inc<ASource>,
    B: Inc<BSource>,
    C: Inc<CSource>,
    D: Inc<DSource>,
    E: Inc<ESource>,
    F: Inc<FSource>,
> Inc<Source> for (A, B, C, D, E, F) {
    fn fresh_eval(source: Source) -> Self {
        let (a_source, b_source, c_source, d_source, e_source, f_source) = source.shallow_eval();
        (
            A::fresh_eval(a_source),
            B::fresh_eval(b_source),
            C::fresh_eval(c_source),
            D::fresh_eval(d_source),
            E::fresh_eval(e_source),
            F::fresh_eval(f_source),
        )
    }

    fn re_eval(&mut self, source: Source) {
        let (a_source, b_source, c_source, d_source, e_source, f_source) = source.shallow_eval();
        self.0.re_eval(a_source);
        self.1.re_eval(b_source);
        self.2.re_eval(c_source);
        self.3.re_eval(d_source);
        self.4.re_eval(e_source);
        self.5.re_eval(f_source);
    }
}

impl<
    ASource,
    BSource,
    CSource,
    DSource,
    ESource,
    FSource,
    GSource,
    Source: ShallowEval<Output = (ASource, BSource, CSource, DSource, ESource, FSource, GSource)>,
    A: Inc<ASource>,
    B: Inc<BSource>,
    C: Inc<CSource>,
    D: Inc<DSource>,
    E: Inc<ESource>,
    F: Inc<FSource>,
    G: Inc<GSource>,
> Inc<Source> for (A, B, C, D, E, F, G) {
    fn fresh_eval(source: Source) -> Self {
        let (a_source, b_source, c_source, d_source, e_source, f_source, g_source) =
            source.shallow_eval();
        (
            A::fresh_eval(a_source),
            B::fresh_eval(b_source),
            C::fresh_eval(c_source),
            D::fresh_eval(d_source),
            E::fresh_eval(e_source),
            F::fresh_eval(f_source),
            G::fresh_eval(g_source),
        )
    }

    fn re_eval(&mut self, source: Source) {
        let (a_source, b_source, c_source, d_source, e_source, f_source, g_source) =
            source.shallow_eval();
        self.0.re_eval(a_source);
        self.1.re_eval(b_source);
        self.2.re_eval(c_source);
        self.3.re_eval(d_source);
        self.4.re_eval(e_source);
        self.5.re_eval(f_source);
        self.6.re_eval(g_source);
    }
}

impl<
    ASource,
    BSource,
    CSource,
    DSource,
    ESource,
    FSource,
    GSource,
    HSource,
    Source: ShallowEval<Output = (
        ASource,
        BSource,
        CSource,
        DSource,
        ESource,
        FSource,
        GSource,
        HSource,
    )>,
    A: Inc<ASource>,
    B: Inc<BSource>,
    C: Inc<CSource>,
    D: Inc<DSource>,
    E: Inc<ESource>,
    F: Inc<FSource>,
    G: Inc<GSource>,
    H: Inc<HSource>,
> Inc<Source> for (A, B, C, D, E, F, G, H) {
    fn fresh_eval(source: Source) -> Self {
        let (a_source, b_source, c_source, d_source, e_source, f_source, g_source, h_source) =
            source.shallow_eval();
        (
            A::fresh_eval(a_source),
            B::fresh_eval(b_source),
            C::fresh_eval(c_source),
            D::fresh_eval(d_source),
            E::fresh_eval(e_source),
            F::fresh_eval(f_source),
            G::fresh_eval(g_source),
            H::fresh_eval(h_source)
        )
    }

    fn re_eval(&mut self, source: Source) {
        let (a_source, b_source, c_source, d_source, e_source, f_source, g_source, h_source) =
            source.shallow_eval();
        self.0.re_eval(a_source);
        self.1.re_eval(b_source);
        self.2.re_eval(c_source);
        self.3.re_eval(d_source);
        self.4.re_eval(e_source);
        self.5.re_eval(f_source);
        self.6.re_eval(g_source);
        self.7.re_eval(h_source);
    }
}
