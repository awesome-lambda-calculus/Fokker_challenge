import FokkerChallenge.BetaCheck
import FokkerChallenge.DBNotation

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


/-- Certificates for terms 193–288 of the solved part of `undecided_terms.json`. -/
def fokkerCerts9 : List (Term String × List (Term String)) :=
  [
    (db! "λλλλ233", [db! "λλ(λλλ2)(011)", db! "λλλλ233"]),
    (db! "λλλλ323", [db! "λλ(λλλ2)(101)", db! "λλλλ323"]),
    (db! "λλλλ332", [db! "λλ(λλλ2)(110)", db! "λλλλ332"]),
    (db! "λλλ1122", [db! "λλ(λλ1)(0011)", db! "λλλ1122"]),
    (db! "λλλ1212", [db! "λλ(λλ1)(0101)", db! "λλλ1212"]),
    (db! "λλλ1221", [db! "λλ(λλ1)(0110)", db! "λλλ1221"]),
    (db! "λλλ1222", [db! "λλ(λλ1)(0111)", db! "λλλ1222"]),
    (db! "λλλ2112", [db! "λλ(λλ1)(1001)", db! "λλλ2112"]),
    (db! "λλλ2121", [db! "λλ(λλ1)(1010)", db! "λλλ2121"]),
    (db! "λλλ2122", [db! "λλ(λλ1)(1011)", db! "λλλ2122"]),
    (db! "λλλ2211", [db! "λλ(λλ1)(1100)", db! "λλλ2211"]),
    (db! "λλλ2212", [db! "λλ(λλ1)(1101)", db! "λλλ2212"]),
    (db! "λλλ2221", [db! "λλ(λλ1)(1110)", db! "λλλ2221"]),
    (db! "λλ1(λ122)", [db! "λλ1((λλ1)(011))", db! "λλ1(λ122)"]),
    (db! "λλ1(λ212)", [db! "λλ1((λλ1)(101))", db! "λλ1(λ212)"]),
    (db! "λλ1(λ221)", [db! "λλ1((λλ1)(110))", db! "λλ1(λ221)"]),
    (db! "λλ(λ122)1", [db! "λλ(λλ1)(011)1", db! "λλ(λ122)1"]),
    (db! "λλ(λ212)1", [db! "λλ(λλ1)(101)1", db! "λλ(λ212)1"]),
    (db! "λλ(λ221)1", [db! "λλ(λλ1)(110)1", db! "λλ(λ221)1"])
  ]

theorem fokkerCerts9_ok : entriesOK fokkerCerts9 = true := by decide
