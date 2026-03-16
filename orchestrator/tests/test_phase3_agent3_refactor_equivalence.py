"""Regression checks for phase3 modular refactor facade wiring."""

from orchestrator import main
from orchestrator import phase3_agent3
from orchestrator.phase3.escalation import _apply_agent2_route as _apply_agent2_route_split
from orchestrator.phase3.guards import (
    _is_line_still_sorry as _is_line_still_sorry_split,
    _scan_sorry_lines_in_file as _scan_sorry_lines_in_file_split,
)
from orchestrator.phase3.prompting import (
    _build_preemptive_agent7_prompt as _build_preemptive_agent7_prompt_split,
)


def test_main_routes_to_phase3_prove_facade():
    assert main.phase3_prove is phase3_agent3.phase3_prove


def test_phase3_helper_bindings_use_split_modules():
    # Ensure facade-level symbols are now sourced from phase3 submodules.
    assert phase3_agent3._scan_sorry_lines_in_file is _scan_sorry_lines_in_file_split
    assert phase3_agent3._is_line_still_sorry is _is_line_still_sorry_split
    assert phase3_agent3._apply_agent2_route is _apply_agent2_route_split
    assert (
        phase3_agent3._build_preemptive_agent7_prompt
        is _build_preemptive_agent7_prompt_split
    )


def test_phase3_max_turn_budget_constant_stable():
    assert phase3_agent3.MAX_AGENT3_TOOL_TURNS == 20

