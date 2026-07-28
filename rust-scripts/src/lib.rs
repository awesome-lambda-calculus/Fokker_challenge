use lambda_calculus::term::*;
use lambda_calculus::*;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen(getter_with_clone)]
#[derive(Debug, Clone)]
pub struct Res {
    pub encoded: String,
    pub debruijn: String,
    pub fokker_size: usize,
    pub lc: bool,
    pub all0: bool,
    pub no_duplicate: bool,
    pub every_bvar_is_used: bool,
    pub only_one_var_used: bool,
    pub has_beta_redex: bool,
    pub eta_normal_form: Option<String>,
    pub two_vars_are_enough: bool,
    pub xy_representation: Option<String>,
    pub code_template: String,
}

pub fn parse_term(x: &str) -> Option<Term> {
    let x = x.replace("Term.app", " ");
    let x = x.replace("Term.bvar", " ");
    let x = x.replace("Term.abs", "λ");

    let x = x.replace(".app", " ");
    let x = x.replace(".bvar", " ");
    let x = x.replace(".abs", "λ");

    let x = x.replace("app", " ");
    let x = x.replace("bvar", " ");
    let x = x.replace("abs", "λ");

    let x = x.replace("var", " ");
    let x = x.replace("lam", "λ");

    let xs: Vec<char> = x.trim().chars().collect();

    if let Ok(a) = parse(&x, DeBruijn) {
        Some(a)
    } else if let Ok(a) = parse(&x, Classic) {
        Some(a)
    } else if let Some((a, _)) = Term::decode_fuel(&xs) {
        Some(a)
    } else {
        None
    }
}

#[wasm_bindgen]
pub fn parse_term_in_any_format(x: &str) -> Option<Res> {
    let t = parse_term(x)?;

    let eta_normal_form = match t.lc() {
        true => match t.has_eta_redex() {
            true => {
                let x = t.clone().eta_reduce();
                assert!(x.lc());
                assert_ne!(t, x);
                Some(format!("{:?}", x))
            }
            false => None,
        },
        false => None,
    };

    let res = Res {
        encoded: t.encode(),
        debruijn: format!("{:?}", t),
        fokker_size: t.fokker_size(),
        lc: t.lc(),
        all0: t.all0(),
        no_duplicate: t.no_duplicate(),
        every_bvar_is_used: t.every_bvar_used(),
        only_one_var_used: t.only_one_var_used(),
        has_beta_redex: t.has_beta_redex(),
        eta_normal_form,
        two_vars_are_enough: t.two_vars_are_enough(),
        xy_representation: t.convert().map(|x| format!("{x}")),
        code_template: format!(
            "def Term_{0}: Term String := {1}

theorem {0}_is_not_basis : not_basis Term_{0} := by sorry",
            t.encode(),
            t.print_lean(),
        ),
    };

    Some(res)
}
