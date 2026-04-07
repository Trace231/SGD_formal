"""Regression tests for guarded Agent8 fresh-error routing."""

from __future__ import annotations

import orchestrator.phase3_agent8 as a8
from orchestrator.phase3_agent8 import _canonical_error_signature, run_agent8_midcheck


def test_canonical_error_signature_prefers_verifier_primary_line():
    errors = (
        "Algorithms/Foo.lean:42:7: error: Application type mismatch\n"
        "Algorithms/Foo.lean:48:2: error: unsolved goals"
    )
    assert _canonical_error_signature(errors) == "Foo.lean:42:application type mismatch"


def test_midcheck_uses_fresh_verify_over_stale_input(monkeypatch, tmp_path):
    monkeypatch.setattr(a8, "AGENT8_ROUTER_MODE", "deterministic")
    target = tmp_path / 'Algo.lean'
    target.write_text('import Mathlib\n\ntheorem t : True := by\n  trivial\n', encoding='utf-8')

    monkeypatch.setattr('orchestrator.tools.run_lean_verify', lambda _path: {
        'errors': 'Algo.lean:4:2: error: unsolved goals',
        'exit_code': 1,
        'sorry_count': 1,
    })

    decision = run_agent8_midcheck(
        str(target),
        'plan',
        'OLD.lean:1:1: error: unknown identifier foo',
        decision_history=[],
        turns_elapsed=3,
    )
    assert decision['error_signature'] == 'Algo.lean:4:unsolved goals'
    assert decision['canonical_error_signature'] == 'Algo.lean:4:unsolved goals'
    assert decision['repair_unit'] == 'local_patch'


def test_midcheck_routes_declaration_errors_to_agent7(monkeypatch, tmp_path):
    monkeypatch.setattr(a8, "AGENT8_ROUTER_MODE", "deterministic")
    target = tmp_path / 'Algo.lean'
    target.write_text('import Mathlib\n\ntheorem t : True := by\n  trivial\n', encoding='utf-8')

    monkeypatch.setattr('orchestrator.tools.run_lean_verify', lambda _path: {
        'errors': 'Algo.lean:3:11: error: unknown identifier foo',
        'exit_code': 1,
        'sorry_count': 0,
    })

    decision = run_agent8_midcheck(str(target), 'plan', 'stale', decision_history=[], turns_elapsed=3)
    assert decision['action'] == 'agent7_signature'
    assert decision['repair_unit'] == 'local_patch'


def test_midcheck_promotes_stalled_proof_to_search(monkeypatch, tmp_path):
    monkeypatch.setattr(a8, "AGENT8_ROUTER_MODE", "deterministic")
    target = tmp_path / 'Algo.lean'
    target.write_text('import Mathlib\n\ntheorem t : True := by\n  trivial\n', encoding='utf-8')

    monkeypatch.setattr('orchestrator.tools.run_lean_verify', lambda _path: {
        'errors': 'Algo.lean:4:2: error: rewrite failed',
        'exit_code': 1,
        'sorry_count': 1,
    })

    history = [
        {
            'action': 'agent3_tactical',
            'canonical_error_signature': 'Algo.lean:4:rewrite failed',
            'sorry_before': 1,
            'sorry_after': 1,
            'main_error_signature_changed': False,
        },
        {
            'action': 'agent3_tactical',
            'canonical_error_signature': 'Algo.lean:4:rewrite failed',
            'sorry_before': 1,
            'sorry_after': 1,
            'main_error_signature_changed': False,
        },
    ]

    decision = run_agent8_midcheck(
        str(target),
        'plan',
        'stale',
        decision_history=history,
        turns_elapsed=12,
    )
    assert decision['action'] == 'agent3_tactical'
    assert decision['repair_unit'] == 'block_restructure'
    assert decision['agent3_execution_mode'] == 'search'
