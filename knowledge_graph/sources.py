"""Read-only parsers for knowledge graph data sources.

Uses Strategy pattern: each parser implements a parse() method.
Does NOT import orchestrator.
"""

from __future__ import annotations

import json
import re
from abc import ABC, abstractmethod
from pathlib import Path
from typing import Any, Protocol

from knowledge_graph.config import (
    ALGORITHMS_DIR,
    AUDITS_DIR,
    DOCS_DIR,
    LIB_DIR,
    SEEDS_PATH,
    SGD_ROOT,
)


# ---------------------------------------------------------------------------
# SourceParser protocol
# ---------------------------------------------------------------------------


class SourceParser(Protocol):
    """Protocol for source file parsers."""

    def parse(self, path: Path | None = None) -> Any:
        """Parse the source and return structured data. Path may be optional."""
        ...


# ---------------------------------------------------------------------------
# Catalog parser
# ---------------------------------------------------------------------------


class CatalogParser:
    """Parse docs/CATALOG.md for algorithms, glue, and roadmap."""

    _ALGO_HEADING_RE = re.compile(
        r"^## Algorithm Layer \(Layer 2\) — `Algorithms/([^`]+)\.lean`",
        re.MULTILINE,
    )
    _ARCHETYPE_RE = re.compile(r"Archetype ([AB])", re.IGNORECASE)
    _LEVERAGE_RE = re.compile(
        r"reused?\s*(?:existing)?[^=]*=\s*(\d+).*?new[^=]*=\s*(\d+)",
        re.IGNORECASE | re.DOTALL,
    )
    # Fallback for "reuse ratio = `$N / (N + M) = ...`" format (with optional spaces)
    _LEVERAGE_RATIO_RE = re.compile(
        r"reuse ratio\s*=\s*[^0-9]*(\d+)\s*/\s*\((\d+)\s*\+\s*(\d+)\)",
        re.IGNORECASE,
    )
    _LEMMA_HEADING_RE = re.compile(r"^#### `([^`]+)`", re.MULTILINE)
    _HIT_ROW_RE = re.compile(
        r"\|\s*`?([^`|]+)`?\s*\|\s*`?([^`|]+)`?\s*\|",
        re.MULTILINE,
    )

    def parse(self, path: Path | None = None) -> dict[str, Any]:
        catalog_path = path or DOCS_DIR / "CATALOG.md"
        if not catalog_path.exists():
            return {"algorithms": [], "glue": [], "roadmap": {}, "catalog_claims": []}

        content = catalog_path.read_text(encoding="utf-8")
        algorithms = self._parse_algorithms(content)
        self._supplement_algorithms(content, algorithms)
        glue = self._parse_glue(content)
        roadmap, roadmap_claims = self._parse_roadmap(content)
        hit_claims = self.get_catalog_claims_from_algorithms(algorithms)
        catalog_claims = list(set(roadmap_claims + [(a, s) for a, s, _ in hit_claims]))
        return {
            "algorithms": algorithms,
            "glue": glue,
            "roadmap": roadmap,
            "catalog_claims": catalog_claims,
            "hit_claims": hit_claims,
        }

    def _parse_algorithms(self, content: str) -> list[dict]:
        algorithms = []
        for m in self._ALGO_HEADING_RE.finditer(content):
            algo_name = m.group(1).replace(".lean", "")
            section_end = content.find("\n## ", m.end())
            section = content[m.start() : (section_end if section_end >= 0 else len(content))]

            archetype_m = self._ARCHETYPE_RE.search(section)
            archetype = archetype_m.group(1).upper() if archetype_m else ""

            leverage_m = self._LEVERAGE_RE.search(section)
            if leverage_m:
                reused = int(leverage_m.group(1))
                new_count = int(leverage_m.group(2))
            else:
                ratio_m = self._LEVERAGE_RATIO_RE.search(section)
                if ratio_m:
                    reused = int(ratio_m.group(2))
                    new_count = int(ratio_m.group(3))
                else:
                    reused, new_count = 0, 0
            leverage = reused / (reused + new_count) if (reused + new_count) > 0 else 0.0

            update_rule = ""
            proof_sketch = ""
            glue_used = []

            if "Conclusion" in section:
                concl_m = re.search(r"\|\s*Conclusion\s*\|\s*`([^`]*)`", section)
                if concl_m:
                    update_rule = concl_m.group(1).strip()
            if "Call chain" in section:
                chain_m = re.search(r"Call chain \|\s*([^\n|]+)", section)
                if chain_m:
                    proof_sketch = chain_m.group(1).strip()
                elif "**Call chain:**" in section or "**Call chain (" in section:
                    chain_block = re.search(
                        r"\*\*Call chain[^:]*:\*\*\s*```?\s*([^`]+)```?",
                        section,
                        re.DOTALL,
                    )
                    if chain_block:
                        proof_sketch = " ".join(chain_block.group(1).strip().split()[:30])

            hit_start = section.find("Hit Report")
            if hit_start >= 0:
                hit_section = section[hit_start : hit_start + 2000]
                for row in hit_section.split("\n"):
                    if "|" in row and "Component" not in row and "---" not in row:
                        parts = [p.strip().strip("`") for p in row.split("|") if p.strip()]
                        if len(parts) >= 2:
                            comp, fpath = parts[0], parts[1]
                            if comp and fpath and not comp.startswith("File"):
                                glue_used.append({"symbol": comp, "file": fpath})

            algorithms.append({
                "algorithm": algo_name,
                "file": f"Algorithms/{algo_name}.lean",
                "archetype": archetype,
                "update_rule": update_rule,
                "proof_sketch": proof_sketch,
                "glue_used": glue_used,
                "leverage_reused": reused,
                "leverage_new": new_count,
                "leverage": leverage,
            })
        return algorithms

    def _supplement_algorithms(self, content: str, algorithms: list[dict]) -> None:
        """For algorithms with empty update_rule/proof_sketch, search full document."""
        algo_by_name = {a["algorithm"]: a for a in algorithms}
        file_pattern = re.compile(r"\|\s*File\s*\|\s*`Algorithms/([^`/]+)\.lean`", re.MULTILINE)
        for m in file_pattern.finditer(content):
            algo_name = m.group(1)
            if algo_name not in algo_by_name:
                continue
            entry = algo_by_name[algo_name]
            block_start = max(0, m.start() - 500)
            block_end = min(len(content), m.end() + 1500)
            block = content[block_start:block_end]
            if not entry.get("update_rule") and "Conclusion" in block:
                concl_m = re.search(r"\|\s*Conclusion\s*\|\s*`([^`]*)`", block)
                if concl_m:
                    entry["update_rule"] = concl_m.group(1).strip()
            if not entry.get("proof_sketch") and "Call chain" in block:
                chain_m = re.search(r"Call chain \|\s*([^\n|]+)", block)
                if chain_m:
                    entry["proof_sketch"] = chain_m.group(1).strip()
                else:
                    chain_block = re.search(
                        r"\*\*Call chain[^:]*:\*\*\s*```?\s*([^`]+)```?",
                        block,
                        re.DOTALL,
                    )
                    if chain_block:
                        lines = chain_block.group(1).strip().split("\n")[:3]
                        entry["proof_sketch"] = " → ".join(
                            line.strip().split("→")[0].strip() for line in lines if line.strip()
                        )

    def get_catalog_claims_from_algorithms(self, algorithms: list[dict]) -> list[tuple[str, str, str]]:
        """From algorithm glue_used, build (algorithm, glue, file) claims."""
        claims = []
        for a in algorithms:
            algo = a.get("algorithm", "")
            for g in a.get("glue_used", []):
                sym = g.get("symbol", "")
                fpath = g.get("file", "")
                if sym:
                    claims.append((algo, sym, fpath))
        return claims

    def _parse_glue(self, content: str) -> list[dict]:
        glue = []
        for m in self._LEMMA_HEADING_RE.finditer(content):
            name = m.group(1)
            section_end = content.find("\n#### ", m.end())
            if section_end < 0:
                section_end = content.find("\n### ", m.end())
            section = content[m.start() : (section_end if section_end >= 0 else len(content))]

            file_path = ""
            purpose = ""
            used_by = ""
            file_m = re.search(r"\|\s*File\s*\|\s*`([^`]+)`", section)
            if file_m:
                file_path = file_m.group(1).strip()
            purpose_m = re.search(r"\*\*Purpose:\*\*\s*([^\n*]+)", section)
            if purpose_m:
                purpose = purpose_m.group(1).strip()
            used_m = re.search(r"\*\*Used by:\*\*\s*([^\n]+)", section)
            if used_m:
                used_by = used_m.group(1).strip()

            glue.append({
                "symbol": name,
                "file": file_path,
                "purpose": purpose,
                "used_by": used_by,
            })
        return glue

    def _parse_roadmap(self, content: str) -> tuple[dict, list[tuple[str, str]]]:
        roadmap: dict[str, dict[str, str]] = {}
        catalog_claims: list[tuple[str, str]] = []

        roadmap_start = content.find("## Roadmap & Dependency Tree")
        if roadmap_start < 0:
            return roadmap, catalog_claims

        roadmap_section = content[roadmap_start : roadmap_start + 8000]
        lines = roadmap_section.split("\n")
        header: list[str] | None = None
        for line in lines:
            if "| Lemma |" in line or "| Component |" in line:
                header = [c.strip() for c in line.split("|") if c.strip()]
                continue
            if "|---" in line:
                continue
            if header and line.strip().startswith("|"):
                cells = [c.strip().strip("`") for c in line.split("|")[1:-1]]
                if len(cells) >= 2:
                    lemma, file_path = cells[0], cells[1]
                    if lemma and not lemma.startswith("*"):
                        if lemma not in roadmap:
                            roadmap[lemma] = {"file": file_path, "algorithms": {}}
                        for j, col in enumerate(cells[2:], start=2):
                            if col and col != "—":
                                algo_col = header[j] if j < len(header) else ""
                                if algo_col:
                                    roadmap[lemma]["algorithms"][algo_col] = col
                                    algo_name = self._column_to_algorithm(algo_col)
                                    if algo_name:
                                        catalog_claims.append((algo_name, lemma))

        return roadmap, catalog_claims

    def _column_to_algorithm(self, col: str) -> str | None:
        m = re.match(r"(\w+)\s+(?:convex|nonconvex|strongly convex|inner|outer|stub)", col, re.I)
        if m:
            return m.group(1)
        if "Subgradient" in col:
            return "SubgradientMethod"
        if "SGD" in col and "WD" not in col and "PGD" not in col:
            return "SGD"
        if "WD" in col or "Weight Decay" in col:
            return "WeightDecaySGD"
        if "PGD" in col:
            return "ProjectedGD"
        if "SVRG" in col:
            return "SVRG"
        return None


# ---------------------------------------------------------------------------
# Audits parser
# ---------------------------------------------------------------------------


class AuditsParser:
    """Parse orchestrator/audits/*.json for run metrics."""

    def parse(self, path: Path | None = None) -> dict[str, list[dict]]:
        audits_dir = path or AUDITS_DIR
        if not audits_dir.exists():
            return {}

        by_algo: dict[str, list[dict]] = {}
        for f in sorted(audits_dir.glob("audit_*.json")):
            try:
                data = json.loads(f.read_text(encoding="utf-8"))
                algo = data.get("algorithm", "")
                if not algo:
                    continue
                if algo not in by_algo:
                    by_algo[algo] = []
                hist = data.get("phase3_execution_history", [])
                failures = data.get("phase3_attempt_failures", [])
                retries = sum(1 for e in hist if e.get("status_code") in ("ERROR", "BLOCKED"))
                by_algo[algo].append({
                    "success": data.get("success", False),
                    "retry_count": retries,
                    "attempt_failures": len(failures),
                    "estimated_tokens": 0,
                    "phase3_execution_history": hist,
                    "phase3_attempt_failures": failures,
                })
            except (json.JSONDecodeError, KeyError):
                continue
        return by_algo


# ---------------------------------------------------------------------------
# Lean Used-in parser
# ---------------------------------------------------------------------------


class LeanUsedInParser:
    """Parse Used-in tags from Algorithms/*.lean and Lib/**/*.lean."""

    _LEMMA_DEF_RE = re.compile(
        r"^(?:theorem|lemma|noncomputable\s+def|def)\s+(\w+)",
        re.MULTILINE,
    )
    _USED_IN_RE = re.compile(
        r"Used in:\s*(?:`([^`]+)`)?\s*(?:\(([^)]+)\))?",
        re.IGNORECASE,
    )

    def parse(self, path: Path | None = None) -> list[tuple[str, str, str, str]]:
        """Return [(caller_file, caller_lemma, target_ref, raw_used_in)]."""
        results = []
        root = path or SGD_ROOT
        lean_files = list((root / "Algorithms").glob("*.lean")) + list(
            (root / "Lib").rglob("*.lean")
        )
        for fp in lean_files:
            rel = str(fp.relative_to(root))
            content = fp.read_text(encoding="utf-8")
            for lemma in self._LEMMA_DEF_RE.findall(content):
                doc = self._get_docstring(content, lemma)
                if "Used in:" not in doc:
                    continue
                for m in self._USED_IN_RE.finditer(doc):
                    target = m.group(1) or ""
                    loc = m.group(2) or ""
                    raw = m.group(0) if m else ""
                    if target or loc:
                        results.append((rel, lemma, f"{target} ({loc})".strip(), raw))
        return results

    def _get_docstring(self, content: str, lemma_name: str) -> str:
        pattern = re.compile(
            r"(/\-\-.*?\-/)\s*\n\s*(?:omit\b[^\n]*\n\s*)?"
            r"(?:theorem|lemma|noncomputable\s+def|def)\s+" + re.escape(lemma_name),
            re.DOTALL,
        )
        m = pattern.search(content)
        return m.group(1) if m else ""

    def get_lean_uses(self) -> dict[tuple[str, str], set[str]]:
        """Return {(caller_file, caller_lemma): set of target_lemma_or_file refs}."""
        uses: dict[tuple[str, str], set[str]] = {}
        for caller_file, caller_lemma, target_ref, _ in self.parse():
            key = (caller_file, caller_lemma)
            if key not in uses:
                uses[key] = set()
            if target_ref:
                uses[key].add(target_ref)
        return uses


# ---------------------------------------------------------------------------
# Methodology parser
# ---------------------------------------------------------------------------


class MethodologyParser:
    """Parse docs/METHODOLOGY.md for assumptions and method descriptions."""

    def parse(self, path: Path | None = None) -> dict[str, dict]:
        methodology_path = path or DOCS_DIR / "METHODOLOGY.md"
        if not methodology_path.exists():
            return {}

        content = methodology_path.read_text(encoding="utf-8")
        sections = re.split(r"### Phase \d+[a-z]? — ", content, flags=re.IGNORECASE)
        result = {}
        for section in sections[1:]:
            lines = section.split("\n")
            first_line = lines[0].strip()
            algo_name = self._normalize_algo_name(first_line)
            method = ""
            output = ""
            in_output = False
            output_lines = []
            for line in lines:
                if line.strip().startswith("**Method:**"):
                    in_output = False
                    method = line.replace("**Method:**", "").strip()
                elif line.strip().startswith("**Output:**"):
                    in_output = True
                    output_lines = [line.replace("**Output:**", "").strip()]
                elif in_output and line.strip() and not line.strip().startswith("**"):
                    output_lines.append(line.strip())
                else:
                    in_output = False
            if output_lines:
                output = " ".join(output_lines)
                formula = re.search(r"\$\$[^$]+\$\$|\$[^$]+\$", output)
                if formula:
                    output = formula.group(0)
            result[algo_name] = {"method": method, "output": output}
        return result

    def _normalize_algo_name(self, s: str) -> str:
        s = s.strip()
        # Strip trailing parenthetical qualifiers like "(complete)" or "(next)"
        s = re.sub(r"\s*\([^)]*\)$", "", s).strip()
        if "Clipped" in s or "clipped" in s:
            return "ClippedSGD"
        if "Subgradient" in s:
            return "SubgradientMethod"
        if "SVRG" in s and "Outer" in s:
            return "SVRGOuterLoop"
        if "SVRG" in s:
            return "SVRG"
        if "Weight Decay" in s or "WD" in s:
            return "WeightDecaySGD"
        if "Projected" in s or "PGD" in s:
            return "ProjectedGD"
        if "SGD" in s and "Weight" not in s and "WD" not in s:
            return "SGD"
        return s.replace(" ", "")


# ---------------------------------------------------------------------------
# Planned algorithms parser
# ---------------------------------------------------------------------------


class PlannedAlgorithmsParser:
    """Parse seeds/planned.json for algorithms not yet in CATALOG."""

    def parse(self, path: Path | None = None) -> dict[str, dict]:
        seeds_path = path or SEEDS_PATH
        if not seeds_path.exists():
            return {}
        try:
            data = json.loads(seeds_path.read_text(encoding="utf-8"))
            return dict(data) if isinstance(data, dict) else {}
        except (json.JSONDecodeError, TypeError):
            return {}


# ---------------------------------------------------------------------------
# Parser registry
# ---------------------------------------------------------------------------


PARSERS: dict[str, SourceParser] = {
    "catalog": CatalogParser(),
    "audits": AuditsParser(),
    "lean": LeanUsedInParser(),
    "methodology": MethodologyParser(),
    "planned": PlannedAlgorithmsParser(),
}


def parse_all() -> dict[str, Any]:
    """Run all parsers and return combined data."""
    catalog_data = PARSERS["catalog"].parse()
    audits_data = PARSERS["audits"].parse()
    lean_parser = PARSERS["lean"]
    lean_uses = lean_parser.get_lean_uses() if hasattr(lean_parser, "get_lean_uses") else {}
    methodology_data = PARSERS["methodology"].parse()
    planned_data = PARSERS["planned"].parse()

    return {
        "catalog": catalog_data,
        "audits": audits_data,
        "lean_uses": lean_uses,
        "lean_raw": lean_parser.parse(),
        "methodology": methodology_data,
        "planned": planned_data,
    }
