#!/usr/bin/env python3
"""Extract a structured algorithm specification from images or PDF pages.

Usage — from image files
------------------------
    cd SGD_coldstart
    python book/extract_spec.py \\
        --algorithm "ProjectedGradientDescent" \\
        --images path/to/img1.png path/to/img2.png \\
        [--model qwen-vl-max-latest] \\
        [--output book/FOML/ProjectedGradientDescent.json] \\
        [--force]

Usage — from a PDF (scan specific pages)
-----------------------------------------
    python book/extract_spec.py \\
        --pdf path/to/textbook.pdf \\
        --pages "12,14-16,20" \\
        [--algorithm "StochasticMirrorDescent"]   # optional; inferred from content if omitted
        [--dpi 200] \\
        [--force]

Page numbers are 1-indexed.  Ranges like "3-7" are inclusive.

The script calls the Qwen VL multimodal model (via the existing Dashscope
OpenAI-compatible endpoint configured in orchestrator/config.py) and produces
a JSON file matching the schema of book/FOML/StochasticMirrorDescent.json.

Output location defaults to book/FOML/<AlgorithmName>.json.
"""
from __future__ import annotations

import argparse
import base64
import io
import json
import sys
import tempfile
import time
from pathlib import Path

# ---------------------------------------------------------------------------
# Resolve project root so we can import orchestrator.config even when the
# script is run from any working directory.
# ---------------------------------------------------------------------------
_SCRIPT_DIR = Path(__file__).resolve().parent          # book/
_PROJECT_ROOT = _SCRIPT_DIR.parent                     # SGD_coldstart/
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

from openai import OpenAI                              # noqa: E402  (after path fix)

try:
    from orchestrator.config import API_KEYS, PROVIDER_URLS
    _QWEN_API_KEY = API_KEYS.get("qwen", "")
    _QWEN_BASE_URL = PROVIDER_URLS.get("qwen", "https://dashscope.aliyuncs.com/compatible-mode/v1")
except Exception:
    import os
    _QWEN_API_KEY = os.getenv("QWEN_API_KEY", "")
    _QWEN_BASE_URL = "https://dashscope.aliyuncs.com/compatible-mode/v1"

DEFAULT_MODEL = "qwen3.5-plus"
MAX_RETRIES = 3
RETRY_DELAYS = (3, 6, 12)   # seconds

# ---------------------------------------------------------------------------
# JSON schema description (injected into the system prompt)
# ---------------------------------------------------------------------------

_SCHEMA_DESCRIPTION = """
The output JSON MUST follow this exact top-level schema:

{
  "algorithm": "<PascalCase identifier, e.g. StochasticMirrorDescent>",
  "full_name": "<Human-readable full name with variant, e.g. 'SGD (Convex, Constant Step Size)'>",
  "source_reference": "<Book/paper title + chapter/theorem reference>",
  "lean_theorem": "TBD",
  "archetype": "<'A' if reduces to plain SGD oracle variant, 'B' if novel update structure>",
  "archetype_note": "<1-2 sentence justification of the archetype classification>",
  "formalization_status": "not_started",
  "formalization_difficulty": "<'low' | 'medium' | 'high'>",
  "prerequisite_lib_work": [
    "<Each item is one Lean 4 library definition or lemma that must be built before the main proof>"
  ],
  "sections": {
    "1_assumptions": {
      "title": "Assumptions and Context",
      "<key>": {
        "description": "<Mathematical description of this assumption>",
        "note": "<Optional extra context>"
      }
      // ... one entry per distinct assumption group (space, function, oracle, step sizes, etc.)
    },
    "2_algorithm": {
      "title": "Algorithm Specification",
      "initialization": "<x_1 ∈ X or equivalent>",
      "update_rule": {
        "math": "<LaTeX formula for x_{t+1}>",
        "ref": "<equation number in source if available>",
        "interpretation": "<1 sentence plain-English description>",
        "note": "<optional special case or reduction>"
      },
      "output": {
        "math": "<LaTeX formula for the output point or average>",
        "ref": "<equation number>",
        "description": "<what the output represents>",
        "note": "<why this output is used>"
      }
    },
    "3_key_lemma_chain": {
      "title": "Key Lemma Chain",
      "overview": "<1-2 sentence summary of proof strategy>",
      "<lemma_id>": {
        "id": "<short identifier>",
        "title": "<human-readable lemma name>",
        "statement_math": "<LaTeX inequality or equation>",
        "proof_sketch": ["<step 1>", "<step 2>", "..."],
        "key_technique": "<main proof technique used>",
        "proof_technique": "<one of: novel_construction | telescoping_sum | induction | direct_calc | martingale>"
      }
      // ... one entry per key lemma or proof step
    },
    "4_final_theorem": {
      "title": "Final Convergence Theorem",
      "lean_identifier": "TBD",
      "ref": "<theorem number in source>",
      "statement_math": "<LaTeX full convergence bound>",
      "interpretation": {
        "first_term": "<what the first term in the bound represents>",
        "second_term": "<what the second term represents>",
        "rate": "<asymptotic rate, e.g. O(1/sqrt(T))>"
      },
      "proof_dependency_summary": {
        "new_lib_required": ["<each new Lean 4 definition/lemma needed>"],
        "mathlib_lemmas": ["<existing Mathlib lemmas that will be used>"],
        "patterns_used": ["<proof patterns from GLUE_TRICKS.md that apply>"]
      },
      "formalization_roadmap": {
        "phase_1": "<first Lean 4 file to build and what it contains>",
        "phase_2": "<second file>",
        "phase_3": "<third file, usually the main algorithm file>",
        "note": "<key blocker or dependency note>"
      }
    }
  }
}

IMPORTANT rules:
- Use LaTeX notation inside string values (\\\\langle, \\\\rangle, \\\\sum, etc.).
- Every mathematical formula goes in a "math" or "statement_math" field.
- Extract ALL lemmas and proof steps from the images — do not summarize or skip any.
- "prerequisite_lib_work" lists concrete Lean 4 definitions, not vague tasks.
- Output ONLY the JSON object — no markdown fences, no prose before or after.
"""

_SYSTEM_PROMPT = (
    "You are a mathematical formalization assistant specializing in converting "
    "textbook algorithm proofs into structured JSON specifications for Lean 4 "
    "formal verification.\n\n"
    "You will receive one or more images containing: the algorithm description, "
    "all key lemmas, and the main convergence theorem.\n\n"
    "Your task: extract every piece of mathematical content from the images and "
    "output a single structured JSON object.\n\n"
    + _SCHEMA_DESCRIPTION
)

# ---------------------------------------------------------------------------
# PDF → image conversion
# ---------------------------------------------------------------------------

def _parse_page_spec(spec: str) -> list[int]:
    """Parse a comma-separated page spec like "1,3-5,8" into a sorted list of
    0-indexed page numbers (pymupdf convention).

    Input numbers are 1-indexed (human-friendly).
    """
    pages: list[int] = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            lo, hi = part.split("-", 1)
            pages.extend(range(int(lo) - 1, int(hi)))   # convert to 0-indexed
        else:
            pages.append(int(part) - 1)
    return sorted(set(pages))


def pdf_pages_to_images(
    pdf_path: str | Path,
    pages: list[int],
    dpi: int = 200,
) -> list[Path]:
    """Render the specified (0-indexed) PDF pages to PNG files in a temp dir.

    Returns a list of Path objects for the rendered PNG files, in page order.
    The caller is responsible for cleaning up the temp dir if desired; here we
    use a persistent tempdir so the files survive until the process exits.
    """
    try:
        import fitz  # pymupdf
    except ImportError as exc:
        raise ImportError(
            "pymupdf is required for PDF support. Install it with: pip install pymupdf"
        ) from exc

    pdf_path = Path(pdf_path)
    if not pdf_path.exists():
        raise FileNotFoundError(f"PDF not found: {pdf_path}")

    doc = fitz.open(str(pdf_path))
    total = doc.page_count
    out_paths: list[Path] = []

    tmp_dir = Path(tempfile.mkdtemp(prefix="extract_spec_pdf_"))
    mat = fitz.Matrix(dpi / 72, dpi / 72)   # 72 dpi is pymupdf default

    for page_idx in pages:
        if page_idx < 0 or page_idx >= total:
            print(
                f"[extract_spec] WARNING: page {page_idx + 1} is out of range "
                f"(PDF has {total} pages). Skipping.",
                file=sys.stderr,
            )
            continue
        page = doc[page_idx]
        pix = page.get_pixmap(matrix=mat)
        out_file = tmp_dir / f"page_{page_idx + 1:04d}.png"
        pix.save(str(out_file))
        out_paths.append(out_file)
        print(f"[extract_spec] Rendered PDF page {page_idx + 1} → {out_file.name}")

    doc.close()
    return out_paths


# ---------------------------------------------------------------------------
# Image utilities
# ---------------------------------------------------------------------------

_MIME_MAP = {
    "jpg": "image/jpeg",
    "jpeg": "image/jpeg",
    "png": "image/png",
    "gif": "image/gif",
    "webp": "image/webp",
}


def _encode_image(path: str | Path) -> tuple[str, str]:
    """Return (base64_string, mime_type) for the given image file."""
    p = Path(path)
    ext = p.suffix.lower().lstrip(".")
    mime = _MIME_MAP.get(ext, "image/jpeg")
    data = base64.standard_b64encode(p.read_bytes()).decode()
    return data, mime


def _image_message_part(path: str | Path) -> dict:
    """Build an OpenAI-style image_url message part from a local file."""
    b64, mime = _encode_image(path)
    return {
        "type": "image_url",
        "image_url": {"url": f"data:{mime};base64,{b64}"},
    }


# ---------------------------------------------------------------------------
# JSON parsing helpers
# ---------------------------------------------------------------------------

def _strip_fences(text: str) -> str:
    """Remove leading/trailing markdown code fences if present."""
    text = text.strip()
    if text.startswith("```"):
        lines = text.splitlines()
        # Drop first line (```json or ```) and last line (```)
        inner = lines[1:] if lines[-1].strip() == "```" else lines[1:]
        text = "\n".join(ln for ln in inner if not ln.strip() == "```").strip()
    return text


_REQUIRED_TOP_KEYS = {"algorithm", "sections"}
_REQUIRED_SECTION_KEYS = {"1_assumptions", "2_algorithm", "3_key_lemma_chain", "4_final_theorem"}


def _validate(obj: object) -> None:
    """Raise ValueError if the parsed object is missing required keys."""
    if not isinstance(obj, dict):
        raise ValueError("Top-level value is not a JSON object")
    missing_top = _REQUIRED_TOP_KEYS - obj.keys()
    if missing_top:
        raise ValueError(f"Missing top-level keys: {missing_top}")
    sections = obj.get("sections", {})
    if not isinstance(sections, dict):
        raise ValueError("'sections' is not an object")
    missing_sec = _REQUIRED_SECTION_KEYS - sections.keys()
    if missing_sec:
        raise ValueError(f"Missing section keys: {missing_sec}")


# ---------------------------------------------------------------------------
# LLM call
# ---------------------------------------------------------------------------

def _build_user_content(
    images: list[str | Path],
    algorithm: str | None,
) -> list[dict]:
    """Build the multimodal content list for the user message."""
    parts: list[dict] = []
    for img in images:
        parts.append(_image_message_part(img))

    if algorithm:
        algo_hint = f"Algorithm name (PascalCase): {algorithm}\n\n"
    else:
        algo_hint = (
            "No algorithm name was provided. "
            "Please infer the algorithm name from the images and use it as the "
            "'algorithm' field (PascalCase, e.g. 'StochasticMirrorDescent').\n\n"
        )

    parts.append({
        "type": "text",
        "text": (
            algo_hint
            + "Please extract all mathematical content from the images above and "
            "produce the structured JSON specification as described in your "
            "system prompt. Include every lemma, assumption, and proof step "
            "shown in the images — do not omit anything.\n\n"
            "Output ONLY the JSON object, no prose, no markdown fences."
        ),
    })
    return parts


def extract_spec(
    algorithm: str | None,
    images: list[str | Path],
    model: str = DEFAULT_MODEL,
) -> dict:
    """Call the multimodal LLM and return the parsed spec dict.

    Retries up to MAX_RETRIES times on parse/validation failure.
    Raises RuntimeError if all attempts fail.
    """
    client = OpenAI(api_key=_QWEN_API_KEY, base_url=_QWEN_BASE_URL)

    user_content = _build_user_content(images, algorithm)
    messages = [{"role": "user", "content": user_content}]
    full_messages = [{"role": "system", "content": _SYSTEM_PROMPT}, *messages]

    last_error: Exception | None = None
    for attempt in range(1, MAX_RETRIES + 1):
        print(f"[extract_spec] Attempt {attempt}/{MAX_RETRIES} — calling {model}...")
        try:
            resp = client.chat.completions.create(
                model=model,
                messages=full_messages,  # type: ignore[arg-type]
                max_tokens=8192,
            )
            raw_text: str = resp.choices[0].message.content or ""
        except Exception as exc:
            print(f"[extract_spec] API error: {exc}")
            last_error = exc
            if attempt < MAX_RETRIES:
                time.sleep(RETRY_DELAYS[attempt - 1])
                continue
            raise RuntimeError(
                f"All {MAX_RETRIES} API attempts failed. Last error: {exc}"
            ) from exc

        text = _strip_fences(raw_text)
        try:
            obj = json.loads(text)
            _validate(obj)
            print(f"[extract_spec] Successfully parsed JSON on attempt {attempt}.")
            return obj
        except (json.JSONDecodeError, ValueError) as exc:
            print(f"[extract_spec] Parse/validation error on attempt {attempt}: {exc}")
            last_error = exc
            if attempt < MAX_RETRIES:
                # Add a correction request to the conversation
                messages.append({"role": "assistant", "content": raw_text})
                messages.append({
                    "role": "user",
                    "content": (
                        f"Your previous response had a problem: {exc}\n"
                        "Please output ONLY the corrected JSON object — "
                        "no markdown fences, no prose."
                    ),
                })
                full_messages = [{"role": "system", "content": _SYSTEM_PROMPT}, *messages]
                time.sleep(RETRY_DELAYS[attempt - 1])

    raise RuntimeError(
        f"Failed to obtain valid JSON after {MAX_RETRIES} attempts. "
        f"Last error: {last_error}"
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Extract a structured algorithm spec from images or PDF pages using a "
            "multimodal LLM and save it as a JSON file in book/FOML/."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  # From image files (algorithm name required)\n"
            "  python book/extract_spec.py --algorithm StochasticMirrorDescent \\\n"
            "      --images img1.png img2.png\n\n"
            "  # From PDF pages (algorithm name optional — inferred from content)\n"
            "  python book/extract_spec.py --pdf textbook.pdf --pages '12,14-16,20'\n\n"
            "  # From PDF with explicit name\n"
            "  python book/extract_spec.py --pdf textbook.pdf --pages '12-18' \\\n"
            "      --algorithm MirrorDescent --dpi 250 --force\n"
        ),
    )

    # Input source (mutually exclusive: images vs pdf)
    input_group = parser.add_mutually_exclusive_group(required=True)
    input_group.add_argument(
        "--images",
        nargs="+",
        metavar="IMAGE",
        help="One or more image file paths (PNG, JPEG, WebP, GIF)",
    )
    input_group.add_argument(
        "--pdf",
        metavar="PDF",
        help="PDF file to extract pages from (use with --pages)",
    )

    parser.add_argument(
        "--pages",
        metavar="SPEC",
        help=(
            "Pages to extract from the PDF, 1-indexed. "
            "Supports ranges and comma lists, e.g. '12,14-16,20'. "
            "Required when --pdf is used."
        ),
    )
    parser.add_argument(
        "--dpi",
        type=int,
        default=200,
        help="Resolution for PDF rendering (default: 200 dpi)",
    )
    parser.add_argument(
        "--algorithm",
        default=None,
        help=(
            "Algorithm name in PascalCase (e.g. ProjectedGradientDescent). "
            "Required with --images. Optional with --pdf — if omitted, the LLM "
            "infers the name from the page content."
        ),
    )
    parser.add_argument(
        "--model",
        default=DEFAULT_MODEL,
        help=f"Multimodal model to use (default: {DEFAULT_MODEL})",
    )
    parser.add_argument(
        "--output",
        default=None,
        help=(
            "Output JSON file path. "
            "Defaults to book/FOML/<AlgorithmName>.json relative to project root. "
            "Required when --algorithm is not provided and output cannot be inferred."
        ),
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite existing output file without prompting.",
    )

    args = parser.parse_args()

    # Validate argument combinations
    if args.images and args.algorithm is None:
        parser.error("--algorithm is required when using --images")
    if args.pdf and args.pages is None:
        parser.error("--pages is required when using --pdf")

    # Build image list
    image_paths: list[Path] = []

    if args.images:
        for img in args.images:
            p = Path(img)
            if not p.exists():
                print(f"[extract_spec] ERROR: Image not found: {img}", file=sys.stderr)
                sys.exit(1)
            image_paths.append(p)

    else:  # PDF mode
        page_indices = _parse_page_spec(args.pages)
        if not page_indices:
            print("[extract_spec] ERROR: --pages produced an empty page list.", file=sys.stderr)
            sys.exit(1)
        print(
            f"[extract_spec] PDF      : {args.pdf}\n"
            f"[extract_spec] Pages    : {[p + 1 for p in page_indices]} (1-indexed)"
        )
        image_paths = pdf_pages_to_images(args.pdf, page_indices, dpi=args.dpi)
        if not image_paths:
            print("[extract_spec] ERROR: No pages rendered from PDF.", file=sys.stderr)
            sys.exit(1)

    # Resolve output path — may be deferred until we know the algorithm name
    algorithm: str | None = args.algorithm

    def _resolve_output(algo_name: str) -> Path:
        if args.output:
            return Path(args.output)
        return _PROJECT_ROOT / "book" / "FOML" / f"{algo_name}.json"

    # If algorithm is known up front, check output path now
    if algorithm and not args.output:
        output_path: Path | None = _resolve_output(algorithm)
    elif args.output:
        output_path = Path(args.output)
    else:
        output_path = None   # deferred — determined from LLM response

    if output_path and output_path.exists() and not args.force:
        answer = input(
            f"Output file already exists: {output_path}\nOverwrite? [y/N] "
        ).strip().lower()
        if answer not in ("y", "yes"):
            print("[extract_spec] Aborted.")
            sys.exit(0)

    print(f"[extract_spec] Algorithm : {algorithm or '(infer from content)'}")
    print(f"[extract_spec] Images    : {[str(p) for p in image_paths]}")
    print(f"[extract_spec] Model     : {args.model}")
    print()

    # Run extraction
    spec = extract_spec(algorithm, image_paths, model=args.model)

    # Resolve algorithm name from LLM response when not provided by user
    inferred_algo = spec.get("algorithm", "UnknownAlgorithm")
    if algorithm and spec.get("algorithm") != algorithm:
        print(
            f"[extract_spec] Note: LLM returned algorithm={spec['algorithm']!r}, "
            f"overriding with CLI value {algorithm!r}."
        )
        spec["algorithm"] = algorithm
        inferred_algo = algorithm
    elif not algorithm:
        print(f"[extract_spec] Inferred algorithm name: {inferred_algo!r}")

    # Finalize output path now that we have the algorithm name
    if output_path is None:
        output_path = _resolve_output(inferred_algo)
        if output_path.exists() and not args.force:
            answer = input(
                f"Output file already exists: {output_path}\nOverwrite? [y/N] "
            ).strip().lower()
            if answer not in ("y", "yes"):
                print("[extract_spec] Aborted.")
                sys.exit(0)

    # Write output
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(spec, f, indent=2, ensure_ascii=False)
    print(f"\n[extract_spec] Written to: {output_path}")


if __name__ == "__main__":
    main()
