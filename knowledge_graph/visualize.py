"""Generate HTML graph visualization from graph.json."""

from __future__ import annotations

import json
from pathlib import Path

from knowledge_graph.config import OUTPUT_DIR


def generate_html() -> None:
    """Read graph.json and write output/graph.html with D3 + Dagre layout."""
    graph_path = OUTPUT_DIR / "graph.json"
    if not graph_path.exists():
        raise FileNotFoundError(f"Graph not found: {graph_path}. Run build first.")

    data = json.loads(graph_path.read_text(encoding="utf-8"))
    nodes = data.get("nodes", [])
    edges = data.get("edges", [])

    html = _build_html(nodes, edges)
    (OUTPUT_DIR / "graph.html").write_text(html, encoding="utf-8")


if __name__ == "__main__":
    generate_html()
    print(f"Generated {OUTPUT_DIR / 'graph.html'}")


def _build_html(nodes: list[dict], edges: list[dict]) -> str:
    """Build single-file HTML with D3 force layout (hierarchy by depth)."""
    nodes_json = json.dumps(nodes, ensure_ascii=False)
    edges_json = json.dumps(edges, ensure_ascii=False)

    return f"""<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <script src="https://d3js.org/d3.v7.min.js"></script>
  <style>
    body {{ font-family: system-ui, sans-serif; margin: 0; background: #1a1a2e; color: #eee; }}
    #graph {{ width: 100%; height: 90vh; }}
    .node {{ cursor: pointer; }}
    .node.algorithm {{ fill: #4a90d9; }}
    .node.glue {{ fill: #2ecc71; }}
    .node.layer1 {{ fill: #e67e22; }}
    .node.layer0 {{ fill: #95a5a6; }}
    .node.planned {{ opacity: 0.5; stroke-dasharray: 5,5; }}
    .link {{ fill: none; stroke: #666; stroke-width: 1.5px; }}
    .link.planned {{ stroke-dasharray: 5,5; opacity: 0.6; }}
    .tooltip {{ position: absolute; padding: 8px; background: #333; border-radius: 4px; font-size: 12px; pointer-events: none; z-index: 1000; }}
  </style>
</head>
<body>
  <h2 style="margin: 1rem;">StochOptLib Knowledge Graph</h2>
  <div id="graph"></div>
  <script>
    const nodesData = {nodes_json};
    const edgesData = {edges_json};

    const nodes = nodesData.map((d, i) => ({{ ...d, index: i }}));
    const edges = edgesData.map(e => ({{ ...e }}));

    const width = 1200, height = 800;
    const svg = d3.select("#graph").append("svg").attr("width", width).attr("height", height);
    const container = svg.append("g");

    const zoom = d3.zoom().scaleExtent([0.2, 4]).on("zoom", (e) => container.attr("transform", e.transform));
    svg.call(zoom);

    const depthScale = d3.scalePoint().domain([...new Set(nodes.map(n => n.depth))].sort((a,b)=>a-b)).range([80, height - 80]);

    const simulation = d3.forceSimulation(nodes)
      .force("link", d3.forceLink(edges).id(d => d.id).distance(80))
      .force("charge", d3.forceManyBody().strength(-300))
      .force("x", d3.forceX(width/2).strength(0.1))
      .force("y", d3.forceY(d => depthScale(d.depth || 0)).strength(0.3));

    const link = container.selectAll(".link")
      .data(edges)
      .join("line")
      .attr("class", d => (d.status === "planned" ? "link planned" : "link"));

    const node = container.selectAll(".node")
      .data(nodes)
      .join("rect")
      .attr("class", d => "node " + (d.type || "") + " " + (d.status || ""))
      .attr("width", 100).attr("height", 30).attr("rx", 4).attr("ry", 4)
      .attr("x", -50).attr("y", -15);

    const label = container.selectAll(".label")
      .data(nodes)
      .join("text")
      .attr("class", "label")
      .attr("text-anchor", "middle")
      .attr("fill", "#fff")
      .attr("font-size", 10)
      .text(d => d.id.length > 14 ? d.id.slice(0,11)+"…" : d.id);

    const tooltip = d3.select("body").append("div").attr("class", "tooltip").style("display", "none");
    node.on("mouseover", (e, d) => {{
      tooltip.style("display", "block")
        .html("<b>" + d.id + "</b><br>Type: " + (d.type||"") + "<br>Status: " + (d.status||"implemented") + "<br>File: " + (d.file||"-") + "<br>Depth: " + (d.depth??"-"))
        .style("left", (e.pageX + 10) + "px")
        .style("top", (e.pageY + 10) + "px");
    }}).on("mouseout", () => tooltip.style("display", "none"));

    simulation.on("tick", () => {{
      link.attr("x1", d => d.source.x).attr("y1", d => d.source.y)
          .attr("x2", d => d.target.x).attr("y2", d => d.target.y);
      node.attr("x", d => d.x - 50).attr("y", d => d.y - 15);
      label.attr("x", d => d.x).attr("y", d => d.y + 4);
    }});
  </script>
</body>
</html>
"""
