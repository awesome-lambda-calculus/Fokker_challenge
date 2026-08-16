use chrono::Local;
use lambda_calculus::Term;
use regex::Regex;
use rust_scripts::parse_term;
use serde::{Deserialize, Serialize};
use serde_json;
use std::collections::HashSet;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

#[derive(Serialize, Deserialize, Clone)]
struct MatchItem {
    full_word: String,
    extracted_prefix: String,
}

#[derive(Serialize, Deserialize, Clone)]
struct FileResult {
    filepath: PathBuf,
    matches: Vec<MatchItem>,
}

#[derive(Serialize, Deserialize)]
struct SearchResult {
    search_pattern: String,
    search_time: String,
    folder_scanned: PathBuf,
    total_files_with_matches: usize,
    total_matches_found: usize,
    results: Vec<FileResult>,

    undecided_terms: usize,
    finite_terms: usize,
    terms_with_redex: usize,
}

const UNDECIDED_TERMS_JSON: &str = "../undecided_terms.json";
const FINITE_TERMS_JSON: &str = "../FokkerChallenge/GenFinite/finite.json";
const OTHER_JSON: &str = "../other.json";

fn serialize_terms(terms: Vec<Term>) -> Vec<String> {
    let mut serialized = terms
        .into_iter()
        .map(|term| format!("{:?}", term))
        .collect::<Vec<_>>();
    serialized.sort();
    serialized
}

fn write_terms_to_json_file(terms: Vec<Term>, path: &str) -> std::io::Result<()> {
    let serialized = serialize_terms(terms);
    let json = serde_json::to_string_pretty(&serialized)?;
    fs::write(path, json)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serialize_terms_formats_sorted_strings() {
        let terms = vec![
            parse_term("λx.x").unwrap(),
            parse_term("λx.λy.x").unwrap(),
        ];
        let formatted = serialize_terms(terms);

        assert_eq!(formatted.len(), 2);
        assert!(formatted.iter().all(|s| !s.is_empty()));
    }

    #[test]
    fn write_terms_to_json_file_writes_array() {
        let path = "/tmp/two_vars_terms_test.json";
        let terms = vec![parse_term("λx.x").unwrap()];

        write_terms_to_json_file(terms, path).unwrap();

        let contents = fs::read_to_string(path).unwrap();
        let parsed: Vec<String> = serde_json::from_str(&contents).unwrap();
        assert_eq!(parsed.len(), 1);
        assert!(parsed[0].contains("x"));

        let _ = fs::remove_file(path);
    }
}

fn main() {
    let json_str = fs::read_to_string(UNDECIDED_TERMS_JSON).unwrap();
    let undecided_terms: Vec<String> = serde_json::from_str(&json_str).unwrap();
    let undecided_terms: HashSet<Term> = undecided_terms
        .into_iter()
        .map(|s| parse_term(&s))
        .flatten()
        .collect();

    let json_str = fs::read_to_string(FINITE_TERMS_JSON).unwrap();
    let finite_terms: Vec<String> = serde_json::from_str(&json_str).unwrap();
    let finite_terms: HashSet<Term> = finite_terms
        .into_iter()
        .map(|s| parse_term(&s))
        .flatten()
        .collect();

    let not_finite_terms: HashSet<Term> = &undecided_terms - &finite_terms;

    let (terms_with_redex, other_terms): (Vec<Term>, Vec<Term>) = not_finite_terms
        .into_iter()
        .partition(|t| t.has_beta_redex() || t.has_eta_redex());

    if let Err(e) = write_terms_to_json_file(other_terms, OTHER_JSON) {
        eprintln!("Failed to write {}: {}", OTHER_JSON, e);
    }


    let folder_path = "..";
    let file_extension: &OsStr = OsStr::new("lean");
    let output_file = "basis_extract_result.json";

    let pattern = r"(\w+)_is_not_basis";
    let regex = Regex::new(pattern).expect("Invalid regex");

    let mut results: Vec<FileResult> = Vec::new();
    let mut total_matches = 0;

    println!("Scanning folder: {}", folder_path);

    for entry in WalkDir::new(folder_path).into_iter().filter_map(|e| e.ok()) {
        if !entry.file_type().is_file() {
            continue;
        }

        let path = entry.path();

        if path.extension() != Some(file_extension) {
            continue;
        }

        match fs::read_to_string(path) {
            Ok(content) => {
                let matches: Vec<_> = regex
                    .captures_iter(&content)
                    .filter_map(|cap| cap.get(1).map(|m| m.as_str().to_string()))
                    .collect();

                if !matches.is_empty() {
                    let file_matches: Vec<MatchItem> = matches
                        .iter()
                        .map(|prefix| MatchItem {
                            full_word: format!("{}_is_not_basis", prefix),
                            extracted_prefix: prefix.clone(),
                        })
                        .collect();

                    let file_result = FileResult {
                        filepath: path.to_path_buf(),
                        matches: file_matches,
                    };

                    results.push(file_result);
                    total_matches += matches.len();
                }
            }
            Err(e) => {
                eprintln!("Fail to read file {}: {}", path.display(), e);
            }
        }
    }

    let search_result = SearchResult {
        search_pattern: "_is_not_basis".to_string(),
        search_time: Local::now().format("%Y-%m-%d %H:%M:%S").to_string(),
        folder_scanned: Path::new(folder_path)
            .canonicalize()
            .unwrap_or_else(|_| Path::new(folder_path).to_path_buf()),
        total_files_with_matches: results.len(),
        total_matches_found: total_matches,
        results,
        undecided_terms: undecided_terms.len(),
        finite_terms: finite_terms.len(),
        terms_with_redex: terms_with_redex.len(),
    };

    match serde_json::to_string_pretty(&search_result) {
        Ok(json) => {
            if let Err(e) = fs::write(output_file, json) {
                eprintln!("Failed to write JSON: {}", e);
            } else {
                println!("✅ Processing complete!");
                println!("   Total prefixes extracted: {}", total_matches);
                println!("   Main output file: {}", output_file);
            }
        }
        Err(e) => eprintln!("Fail serialize JSON: {}", e),
    }

    let found_terms: HashSet<Term> = search_result
        .results
        .iter()
        .flat_map(|fr| fr.matches.iter().map(|m| m.extracted_prefix.clone()))
        .flat_map(|s| parse_term(&s))
        .collect();

    let undecided_terms = &undecided_terms - &found_terms;
    let mut undecided_terms = undecided_terms
        .into_iter()
        .map(|t| format!("{:?}", t))
        .collect::<Vec<_>>();
    undecided_terms.sort();
    fs::write(
        UNDECIDED_TERMS_JSON,
        serde_json::to_string_pretty(&undecided_terms).unwrap(),
    )
    .unwrap();

    let finite_terms = &finite_terms - &found_terms;
    let mut finite_terms = finite_terms
        .into_iter()
        .map(|t| format!("{:?}", t))
        .collect::<Vec<_>>();
    finite_terms.sort();
    fs::write(
        FINITE_TERMS_JSON,
        serde_json::to_string_pretty(&finite_terms).unwrap(),
    )
    .unwrap();
}
