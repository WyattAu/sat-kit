//! DIMACS CNF parsing: `c` comments, `p cnf <vars> <clauses>` header,
//! clauses as whitespace-separated nonzero ints terminated by `0`.

use crate::Lit;

#[derive(Debug, PartialEq)]
pub struct Dimacs {
    pub n_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
}

#[derive(Debug)]
pub enum ParseError {
    NoHeader,
    BadHeader(String),
    LiteralOutOfRange { lit: i32, n_vars: usize },
    UnterminatedClause,
}

pub fn parse(input: &str) -> Result<Dimacs, ParseError> {
    let mut n_vars = 0usize;
    let mut n_clauses_declared = 0usize;
    let mut saw_header = false;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut cur: Vec<Lit> = Vec::new();
    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if !saw_header {
            if line.starts_with('p') {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() < 4 || parts[1] != "cnf" {
                    return Err(ParseError::BadHeader(line.to_string()));
                }
                n_vars = parts[2]
                    .parse()
                    .map_err(|_| ParseError::BadHeader(line.to_string()))?;
                n_clauses_declared = parts[3]
                    .parse()
                    .map_err(|_| ParseError::BadHeader(line.to_string()))?;
                saw_header = true;
                clauses = Vec::with_capacity(n_clauses_declared);
            }
            continue;
        }
        for tok in line.split_whitespace() {
            let l: i32 = tok
                .parse()
                .map_err(|_| ParseError::BadHeader(format!("bad literal token {tok}")))?;
            if l == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                if l.unsigned_abs() as usize > n_vars {
                    return Err(ParseError::LiteralOutOfRange { lit: l, n_vars });
                }
                cur.push(l);
            }
        }
    }
    if !saw_header {
        return Err(ParseError::NoHeader);
    }
    if !cur.is_empty() {
        return Err(ParseError::UnterminatedClause);
    }
    Ok(Dimacs { n_vars, clauses })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_simple_file() {
        let d = parse("c comment\np cnf 3 2\n1 -2 0\n3 0\n").unwrap();
        assert_eq!(d.n_vars, 3);
        assert_eq!(d.clauses, vec![vec![1, -2], vec![3]]);
    }

    #[test]
    fn clause_spanning_lines() {
        let d = parse("p cnf 2 1\n1 2\n-1 0\n").unwrap();
        assert_eq!(d.clauses, vec![vec![1, 2, -1]]);
    }

    #[test]
    fn rejects_out_of_range() {
        assert!(matches!(
            parse("p cnf 2 1\n5 0\n"),
            Err(ParseError::LiteralOutOfRange { lit: 5, n_vars: 2 })
        ));
    }

    #[test]
    fn rejects_missing_header() {
        assert!(matches!(parse("1 0\n"), Err(ParseError::NoHeader)));
    }
}
