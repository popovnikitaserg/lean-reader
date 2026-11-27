from pathlib import Path
import json
import networkx as nx

from lean2graph.source.comments import tokenize_comments
from lean2graph.graphs.proof_claim import ProofClaimGraph


def test_nested_comments_tokenizer() -> None:
    source = "theorem t : True := by -- outer\n  /- outer {- inner -/ end -/\n  trivial"
    comments = tokenize_comments(source)
    assert len(comments) == 2
    assert "inner" in comments[1].text


def test_proof_claim_graph_have_exact(tmp_path: Path) -> None:
    graph = ProofClaimGraph("project-test", "have_exact")
    graph.add_declaration(
        {
            "name": "have_exact",
            "module": "Main",
            "kind": "thm",
            "type_pretty": "p ∧ q",
            "range": None,
        },
        [
            (
                "step-1",
                json.dumps(
                    {
                        "ordinal": 1,
                        "synthetic_syntax": False,
                        "tactic_text": "have hpq : p ∧ q := ⟨hp, hq⟩",
                        "syntax_kind": "Lean.Parser.Tactic.tacticHave__",
                        "range": {"start": {"line": 2, "column": 2}},
                        "assignments": [
                        {"kind": "direct", "expr_pretty": "And.intro hp hq"}
                        ],
                        "goals_before": [
                            {"locals": [], "target_pretty": "p ∧ q"}
                        ],
                        "goals_after": [
                            {
                                "locals": [
                                    {
                                        "fvar_id": "_uniq.1",
                                        "user_name": "hpq",
                                        "type_pretty": "p ∧ q",
                                        "type_expr_id": "expr:hpq:type",
                                    }
                                ],
                                "target_pretty": "p ∧ q",
                            }
                        ],
                        "status": "complete",
                    }
                ),
            ),
            (
                "step-2",
                json.dumps(
                    {
                        "ordinal": 2,
                        "synthetic_syntax": False,
                        "tactic_text": "exact hpq",
                        "syntax_kind": "Lean.Parser.Tactic.exact",
                        "range": {"start": {"line": 3, "column": 2}},
                        "assignments": [
                        {"kind": "direct", "expr_pretty": "_fvar.hpq"}
                        ],
                        "goals_after": [],
                        "status": "complete",
                    }
                ),
            ),
        ],
        [],
    )
    json_path, graphml_path = graph.write(tmp_path)
    data = json.loads(json_path.read_text(encoding="utf-8"))
    assert sum(node["kind"] == "claim" for node in data["nodes"]) >= 2
    assert not any(node.get("role") == "hypothesis" for node in data["nodes"])
    assert sum(node["kind"] == "inference" for node in data["nodes"]) == 2
    loaded = nx.read_graphml(graphml_path)
    assert loaded.number_of_nodes() == len(data["nodes"])


def test_statement_claims_and_step_dataflow_use_lean_context(tmp_path: Path) -> None:
    graph = ProofClaimGraph("project-test", "nested")
    graph.add_declaration(
        {
            "name": "nested",
            "module": "Main",
            "kind": "thm",
            "type_pretty": "∀ {t a : ℕ}, 5 ≤ t → a ≤ t → t ≤ t",
            "statement_context": {
                "variables": [
                    {"name": "t", "type_pretty": "ℕ", "inaccessible_name": False},
                    {"name": "a", "type_pretty": "ℕ", "inaccessible_name": False},
                ],
                "assumptions": [
                    {"name": "ht", "type_pretty": "5 ≤ t"},
                    {"name": "ha", "type_pretty": "a ≤ t"},
                ],
                "goal_pretty": "t ≤ t",
            },
            "range": {
                "start": {"line": 1, "column": 0},
                "end": {"line": 6, "column": 0},
            },
        },
        [
            (
                "step-1",
                json.dumps(
                    {
                        "ordinal": 1,
                        "depth": 1,
                        "scope_id": "root",
                        "synthetic_syntax": False,
                        "tactic_text": "have htone : 1 ≤ t := by omega",
                        "syntax_kind": "Lean.Parser.Tactic.tacticHave__",
                        "range": {
                            "start": {"line": 2, "column": 2},
                            "end": {"line": 2, "column": 33},
                        },
                        "introduced_claims": [
                            {
                                "user_name": "htone",
                                "type_pretty": "1 ≤ t",
                                "type_expr_id": "expr:htone:type",
                                "scope_id": "root",
                                "range": {
                                    "start": {"line": 2, "column": 2},
                                    "end": {"line": 2, "column": 33},
                                },
                            }
                        ],
                        "used_fvars": ["ht"],
                        "used_consts": [],
                        "assignments": [
                            {
                                "kind": "direct",
                                "expr_pretty": "by omega",
                            }
                        ],
                    }
                ),
            ),
            (
                "step-2",
                json.dumps(
                    {
                        "ordinal": 2,
                        "depth": 1,
                        "scope_id": "root",
                        "synthetic_syntax": False,
                        "tactic_text": "exact htone",
                        "syntax_kind": "Lean.Parser.Tactic.exact",
                        "range": {
                            "start": {"line": 3, "column": 2},
                            "end": {"line": 3, "column": 13},
                        },
                        "goals_after": [],
                        "used_fvars": ["htone"],
                        "used_consts": [],
                        "assignments": [
                            {
                                "kind": "direct",
                                "expr_pretty": "_fvar.htone",
                            }
                        ],
                    }
                ),
            ),
        ],
        [],
    )
    json_path, _ = graph.write(tmp_path)
    data = json.loads(json_path.read_text(encoding="utf-8"))
    nodes = {node["id"]: node for node in data["nodes"]}
    claims = [node for node in data["nodes"] if node["kind"] == "claim"]
    inferences = [node for node in data["nodes"] if node["kind"] == "inference"]

    assert {node["role"] for node in claims} >= {
        "variable",
        "assumption",
        "intermediate",
        "final_goal",
    }
    assert not any(node["role"] == "hypothesis" for node in claims)
    assert nodes["claim:project-test:nested:variable:0"]["statement_pretty"] == "t : ℕ"
    assert nodes["claim:project-test:nested:assumption:1"]["statement_pretty"] == "5 ≤ t"
    intermediate = next(node for node in claims if node.get("user_name") == "htone")
    assert intermediate["statement_pretty"] == "1 ≤ t"
    assert ":=" not in intermediate["statement_pretty"]
    assert "have" not in intermediate["statement_pretty"]
    assert all(
        not any(token in json.dumps(node, ensure_ascii=False) for token in ("_fvar.", "?m.", "_uniq."))
        for node in data["nodes"]
    )
    assert len(inferences) == 2
    assert any(
        edge["kind"] == "premise"
        and edge["source"] == "claim:project-test:nested:assumption:1"
        and edge["target"] == inferences[0]["id"]
        for edge in data["edges"]
    )
    assert any(
        edge["kind"] == "conclusion"
        and edge["source"] == inferences[1]["id"]
        and nodes[edge["target"]].get("role") == "final_goal"
        for edge in data["edges"]
    )


def test_calc_rows_use_lean_expected_types(tmp_path: Path) -> None:
    graph = ProofClaimGraph("project-test", "calc_chain")
    graph.add_declaration(
        {
            "name": "calc_chain",
            "module": "Main",
            "kind": "thm",
            "range": {
                "start": {"line": 1, "column": 0},
                "end": {"line": 5, "column": 20},
            },
            "statement_context": {
                "variables": [
                    {"name": name, "type_pretty": "Nat", "type_expr_id": f"expr:{name}"}
                    for name in ("a", "b", "c")
                ],
                "assumptions": [
                    {"name": "hab", "type_pretty": "a ≤ b", "type_expr_id": "expr:hab"},
                    {"name": "hbc", "type_pretty": "b ≤ c", "type_expr_id": "expr:hbc"},
                ],
                "goal_pretty": "a ≤ c",
                "goal_expr_id": "expr:goal",
            },
        },
        [
            (
                "calc",
                json.dumps(
                    {
                        "ordinal": 1,
                        "graph_ordinal": 1,
                        "synthetic_syntax": False,
                        "tactic_text": "calc\n    a ≤ b := hab\n    _ ≤ c := hbc",
                        "syntax_kind": "Lean.calcTactic",
                        "range": {
                            "start": {"line": 2, "column": 2},
                            "end": {"line": 4, "column": 20},
                        },
                        "goals_after": [],
                        "assignments": [{"kind": "direct", "expr_pretty": "proof"}],
                    }
                ),
            )
        ],
        [],
        term_records=[
            {
                "module": "Main",
                "range": {
                    "start": {"line": 3, "column": 17},
                    "end": {"line": 3, "column": 20},
                },
                "expected_type_pretty": "a ≤ b",
                "expected_type_expr_id": "expr:calc:first",
                "expr_id": "expr:hab",
                "expr_pretty": "hab",
                "used_fvars": [{"fvar_id": "f-hab", "user_name": "hab"}],
                "used_consts": [],
            },
            {
                "module": "Main",
                "range": {
                    "start": {"line": 4, "column": 17},
                    "end": {"line": 4, "column": 20},
                },
                "expected_type_pretty": "b ≤ c",
                "expected_type_expr_id": "expr:calc:second",
                "expr_id": "expr:hbc",
                "expr_pretty": "hbc",
                "used_fvars": [{"fvar_id": "f-hbc", "user_name": "hbc"}],
                "used_consts": [],
            },
        ],
        source_text=(
            "theorem calc_chain : a ≤ c := by\n"
            "  calc\n"
            "    a ≤ b := hab\n"
            "    _ ≤ c := hbc\n"
        ),
    )
    json_path, _ = graph.write(tmp_path)
    data = json.loads(json_path.read_text(encoding="utf-8"))
    claims = [
        node for node in data["nodes"]
        if node["kind"] == "claim" and node.get("role") == "intermediate"
    ]
    assert [claim["statement_pretty"] for claim in claims] == ["a ≤ b", "b ≤ c"]
    calc_steps = [
        node for node in data["nodes"]
        if node.get("syntax_kind") == "Lean.calcStep"
    ]
    assert len(calc_steps) == 2
    assert all(step["status"] == "complete" for step in calc_steps)


def test_nested_steps_and_case_scopes_are_preserved(tmp_path: Path) -> None:
    source = (
        "theorem branch_scope (h : P ∨ P) (hp : P) : P := by\n"
        "  cases h with\n"
        "  | inl hp1 =>\n"
        "      have hq : P := by\n"
        "        omega\n"
        "      exact hq\n"
        "  | inr hq =>\n"
        "      exact hp\n"
    )
    graph = ProofClaimGraph("project-test", "branch_scope")
    graph.add_declaration(
        {
            "name": "branch_scope",
            "module": "Main",
            "kind": "thm",
            "type_pretty": "P ∨ P → P → P",
            "statement_context": {
                "variables": [],
                "assumptions": [{"name": "hp", "type_pretty": "P", "fvar_id": "f-hp"}],
                "goal_pretty": "P",
            },
            "range": {
                "start": {"line": 1, "column": 0},
                "end": {"line": 8, "column": 18},
            },
        },
        [
            (
                "cases",
                json.dumps(
                    {
                        "ordinal": 1,
                        "synthetic_syntax": False,
                        "tactic_text": "cases h with",
                        "syntax_kind": "Lean.Parser.Tactic.cases",
                        "range": {
                            "start": {"line": 2, "column": 2},
                            "end": {"line": 8, "column": 18},
                        },
                        "assignments": [{"kind": "direct", "expr_pretty": "proof"}],
                        "goals_after": [{"locals": []}],
                    }
                ),
            ),
            (
                "have",
                json.dumps(
                    {
                        "ordinal": 2,
                        "synthetic_syntax": False,
                        "tactic_text": "have hq : P := by omega",
                        "syntax_kind": "Lean.Parser.Tactic.tacticHave__",
                        "range": {
                            "start": {"line": 4, "column": 6},
                            "end": {"line": 5, "column": 14},
                        },
                        "assignments": [{"kind": "direct", "expr_pretty": "proof"}],
                        "goals_after": [
                            {
                                "locals": [
                                    {
                                        "fvar_id": "f-hq",
                                        "user_name": "hq",
                                        "type_pretty": "P",
                                        "type_expr_id": "expr:hq",
                                    }
                                ]
                            }
                        ],
                    }
                ),
            ),
            (
                "omega",
                json.dumps(
                    {
                        "ordinal": 3,
                        "synthetic_syntax": False,
                        "tactic_text": "omega",
                        "syntax_kind": "Lean.Parser.Tactic.omega",
                        "range": {
                            "start": {"line": 5, "column": 8},
                            "end": {"line": 5, "column": 13},
                        },
                        "assignments": [{"kind": "direct", "expr_pretty": "proof"}],
                        "goals_after": [],
                    }
                ),
            ),
            (
                "exact-hq",
                json.dumps(
                    {
                        "ordinal": 4,
                        "synthetic_syntax": False,
                        "tactic_text": "exact hq",
                        "syntax_kind": "Lean.Parser.Tactic.exact",
                        "range": {
                            "start": {"line": 6, "column": 6},
                            "end": {"line": 6, "column": 14},
                        },
                        "used_fvars": [{"fvar_id": "f-hq", "user_name": "hq"}],
                        "assignments": [{"kind": "direct", "expr_pretty": "hq"}],
                        "goals_after": [],
                    }
                ),
            ),
            (
                "exact-cross-scope",
                json.dumps(
                    {
                        "ordinal": 5,
                        "synthetic_syntax": False,
                        "tactic_text": "exact hp1",
                        "syntax_kind": "Lean.Parser.Tactic.exact",
                        "range": {
                            "start": {"line": 8, "column": 6},
                            "end": {"line": 8, "column": 15},
                        },
                        "used_fvars": [{"fvar_id": "f-hq", "user_name": "hq"}],
                        "assignments": [{"kind": "direct", "expr_pretty": "hq"}],
                        "goals_after": [],
                    }
                ),
            ),
        ],
        [],
        source_text=source,
    )
    json_path, _ = graph.write(tmp_path)
    data = json.loads(json_path.read_text(encoding="utf-8"))
    nodes = {node["id"]: node for node in data["nodes"]}
    by_text = {node.get("tactic_text"): node for node in data["nodes"] if node["kind"] == "inference"}
    assert by_text["omega"]["parent_inference"] == by_text["have hq : P := by omega"]["id"]
    assert by_text["omega"]["depth"] > by_text["have hq : P := by omega"]["depth"]
    assert by_text["have hq : P := by omega"]["scope_id"] == "root/case:inl"
    assert by_text["have hq : P := by omega"]["branch_tag"] == "case:inl"
    cross_scope = by_text["exact hp1"]
    assert cross_scope["scope_id"] == "root/case:inr"
    assert cross_scope["status"] == "partial"
    assert cross_scope["partial_reason"] == "unmapped_fvar"
    assert not any(
        edge["kind"] == "premise"
        and edge["source"] == "claim:project-test:branch_scope:intermediate:2:1"
        and edge["target"] == cross_scope["id"]
        for edge in data["edges"]
    )
    assert any(
        edge["kind"] == "contains"
        and edge["source"] == by_text["have hq : P := by omega"]["id"]
        and edge["target"] == by_text["omega"]["id"]
        for edge in data["edges"]
    )
