"""Compatibility checks for prompts module split into package subfiles."""

from orchestrator import prompts
from orchestrator.prompts.agent3 import AGENT3_PROMPT_TEXT
from orchestrator.prompts.agent8 import AGENT8_PROMPT_TEXT
from orchestrator.prompts.agent9 import AGENT9_PROMPT_TEXT


def test_prompts_module_is_package_init():
    assert prompts.__file__.endswith("/orchestrator/prompts/__init__.py")


def test_split_prompt_bindings_are_preserved():
    # Agent3/8 prompts keep dynamic replacement slots in split source text.
    assert "{AGENT7_CRITERIA}" in AGENT3_PROMPT_TEXT
    assert "{AGENT7_CRITERIA}" not in prompts.SYSTEM_PROMPTS["sorry_closer"]
    assert "{AGENT8_INVESTIGATION_TURNS}" in AGENT8_PROMPT_TEXT
    assert "{AGENT8_INVESTIGATION_TURNS}" not in prompts.SYSTEM_PROMPTS["decision_hub"]
    assert prompts.SYSTEM_PROMPTS["strategy_planner"] == AGENT9_PROMPT_TEXT


def test_key_prompt_phrases_still_present():
    a3 = prompts.SYSTEM_PROMPTS["sorry_closer"]
    a8 = prompts.SYSTEM_PROMPTS["decision_hub"]
    a9 = prompts.SYSTEM_PROMPTS["strategy_planner"]
    assert "You are the Sorry Closer" in a3
    assert "You are the Decision Hub (Agent8)" in a8
    assert "You are the Strategy Planner (Agent9)" in a9
    assert "apollo_decompose_repair" in a8


def test_prompt_tool_signature_examples_match_tools():
    a3_raw = AGENT3_PROMPT_TEXT
    a8_raw = AGENT8_PROMPT_TEXT
    assert "search_codebase(query=" not in a3_raw
    assert 'search_codebase(pattern="<identifier>")' in a3_raw
    assert "current-file evidence" in a3_raw
    assert "canonical error signature" in a8_raw

