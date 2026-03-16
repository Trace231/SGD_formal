"""Routing and escalation helpers for Phase3."""

from __future__ import annotations

from orchestrator.config import ROUTING_PARAMS


def _apply_agent2_route(
    route: dict | None,
    budget: dict,
    last_error_sig: str,
    route_repeat_tracker: dict,
) -> str:
    """Arbitrate Agent2's routing proposal; return the final route_to string.

    Applies the following guardrails in order:
    1. Invalid / missing route → "agent3"
    2. Confidence below threshold → "agent3"
    3. Anti-oscillation: same (error_sig, route_to) pair seen too many times → escalate
    4. "self" budget exceeded → "agent3"
    5. Preemptive Agent7 budget exceeded → "agent3"
    """
    if route is None:
        return "agent3"
    route_to = str(route.get("route_to", "agent3")).strip()
    confidence = float(route.get("confidence", 0.0))
    valid = {"agent3", "agent7", "agent7_then_agent6", "self"}
    if route_to not in valid:
        return "agent3"
    # Low-confidence guard: only route cross-agent when confident enough.
    min_conf = float(ROUTING_PARAMS.get("MIN_CONFIDENCE_FOR_CROSS_AGENT_ROUTE", 0.6))
    if route_to != "agent3" and confidence < min_conf:
        return "agent3"
    # Anti-oscillation: track how many times (error_sig, route_to) has been chosen.
    max_repeat = int(ROUTING_PARAMS.get("MAX_SAME_ROUTE_REPEAT", 2))
    sig_key = f"{last_error_sig[:40]}:{route_to}"
    route_repeat_tracker[sig_key] = route_repeat_tracker.get(sig_key, 0) + 1
    if route_repeat_tracker[sig_key] > max_repeat:
        # Escalate to next level to break oscillation.
        _escalation = {"agent3": "agent7", "agent7": "self", "self": "agent3"}
        return _escalation.get(route_to, "agent3")
    # "self" budget.
    max_self = int(ROUTING_PARAMS.get("MAX_SELF_REVISIONS_PER_ATTEMPT", 1))
    if route_to == "self" and budget.get("self_revisions", 0) >= max_self:
        return "agent3"
    # Preemptive Agent7 budget.
    max_a7 = int(ROUTING_PARAMS.get("AGENT7_PREEMPTIVE_MAX_PER_ATTEMPT", 1))
    if route_to in ("agent7", "agent7_then_agent6") and budget.get("preemptive_agent7", 0) >= max_a7:
        return "agent3"
    return route_to

