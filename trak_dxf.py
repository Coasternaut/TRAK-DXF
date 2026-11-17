#!/usr/bin/env python3
"""
DXF to ProtoTRAK coordinate-sheet generator

Reads LINE, ARC, CIRCLE, LWPOLYLINE, and 2D POLYLINE entities from DXF.
Connected closed profiles are grouped into separate loops and exported to PDF.

Install:
    python -m pip install ezdxf reportlab

Run:
    python dxf_to_prototrak.py

Coordinates are reported in the DXF's drawing units. The program does not
scale, rotate, or convert units.
"""

from dataclasses import dataclass
from math import atan2, cos, sin, pi, sqrt, tan
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog

import ezdxf
from reportlab.lib import colors
from reportlab.lib.pagesizes import portrait, letter
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.lib.units import inch
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
)

from datetime import datetime

@dataclass
class Segment:
    kind: str                   # "LINE" or "ARC"
    sx: float
    sy: float
    ex: float
    ey: float
    cx: float = None
    cy: float = None
    sweep: float = None         # signed degrees; positive = CCW
    source: str = ""

    def reversed(self):
        return Segment(
            self.kind, self.ex, self.ey, self.sx, self.sy,
            self.cx, self.cy,
            -self.sweep if self.sweep is not None else None,
            self.source
        )


def distance(a, b):
    return sqrt((a[0] - b[0]) **  2 + (a[1] - b[1]) ** 2)


def arc_from_angles(cx, cy, radius, start_deg, end_deg, source="ARC"):
    """Create a DXF ARC segment, following DXF's counterclockwise direction."""
    sweep = (end_deg - start_deg) % 360.0
    if abs(sweep) < 1e-10:
        sweep = 360.0
    a1 = start_deg * pi / 180.0
    a2 = (start_deg + sweep) * pi / 180.0
    return Segment(
        "ARC",
        cx + radius * cos(a1), cy + radius * sin(a1),
        cx + radius * cos(a2), cy + radius * sin(a2),
        cx, cy, sweep, source
    )


def bulge_to_segment(p1, p2, bulge, source="POLYLINE"):
    """Convert a polyline bulge into a line or circular arc."""
    x1, y1 = p1
    x2, y2 = p2
    if abs(bulge) < 1e-12:
        return Segment("LINE", x1, y1, x2, y2, source=source)

    dx, dy = x2 - x1, y2 - y1
    chord = sqrt(dx * dx + dy * dy)
    if chord < 1e-12:
        return None

    # Signed included angle is 4*atan(bulge). The center offset is signed.
    offset = chord * (1.0 - bulge * bulge) / (4.0 * bulge)
    mx, my = (x1 + x2) / 2.0, (y1 + y2) / 2.0
    cx = mx - (dy / chord) * offset
    cy = my + (dx / chord) * offset

    a1 = atan2(y1 - cy, x1 - cx)
    sweep = 4.0 * atan2(bulge, 1.0) * 180.0 / pi
    return Segment(
        "ARC", x1, y1, x2, y2, cx, cy, sweep, source
    )


def extract_segments(doc):
    msp = doc.modelspace()
    segments = []
    circles = []
    ignored = {}

    for entity in msp:
        typ = entity.dxftype()
        handle = entity.dxf.get("handle", "")

        if typ == "LINE":
            a, b = entity.dxf.start, entity.dxf.end
            segments.append(Segment(
                "LINE", a.x, a.y, b.x, b.y, source=f"LINE {handle}"
            ))

        elif typ == "ARC":
            c = entity.dxf.center
            segments.append(arc_from_angles(
                c.x, c.y, entity.dxf.radius,
                entity.dxf.start_angle, entity.dxf.end_angle,
                f"ARC {handle}"
            ))

        elif typ == "CIRCLE":
            c = entity.dxf.center
            r = entity.dxf.radius
            # Represent a circle as a full 360-degree arc starting at +X.
            circles.append(Segment(
                "ARC", c.x + r, c.y, c.x + r, c.y,
                c.x, c.y, 360.0, f"CIRCLE {handle}"
            ))

        elif typ == "LWPOLYLINE":
            points = list(entity.get_points("xyb"))
            closed = entity.closed
            count = len(points) if closed else max(0, len(points) - 1)
            for i in range(count):
                p1 = points[i]
                p2 = points[(i + 1) % len(points)]
                seg = bulge_to_segment(
                    (p1[0], p1[1]), (p2[0], p2[1]), p1[2],
                    f"LWPOLYLINE {handle}"
                )
                if seg:
                    segments.append(seg)

        elif typ == "POLYLINE" and not entity.is_3d_polyline:
            verts = list(entity.vertices)
            points = []
            for v in verts:
                loc = v.dxf.location
                bulge = v.dxf.get("bulge", 0.0)
                points.append((loc.x, loc.y, bulge))
            closed = entity.is_closed
            count = len(points) if closed else max(0, len(points) - 1)
            for i in range(count):
                p1 = points[i]
                p2 = points[(i + 1) % len(points)]
                seg = bulge_to_segment(
                    (p1[0], p1[1]), (p2[0], p2[1]), p1[2],
                    f"POLYLINE {handle}"
                )
                if seg:
                    segments.append(seg)

        else:
            # Ignore non-planar or unsupported entity types, but report counts.
            if typ not in ("SEQEND", "VERTEX", "ATTRIB"):
                ignored[typ] = ignored.get(typ, 0) + 1

    return segments, circles, ignored


def cluster_endpoints(segments, tolerance):
    """Assign endpoint node IDs by joining points within the chosen tolerance."""
    points = []
    for seg in segments:
        points.extend([(seg.sx, seg.sy), (seg.ex, seg.ey)])

    parent = list(range(len(points)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    # O(n^2), intentionally simple and suitable for typical 2D part profiles.
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            if distance(points[i], points[j]) <= tolerance:
                union(i, j)

    roots = {}
    node_ids = []
    for i in range(len(points)):
        root = find(i)
        if root not in roots:
            roots[root] = len(roots)
        node_ids.append(roots[root])

    return [(node_ids[2*i], node_ids[2*i+1]) for i in range(len(segments))]


def group_loops(segments, circles, tolerance):
    """Return closed loops and open/disconnected geometry components."""
    loops = [[c] for c in circles]
    if not segments:
        return loops, []

    endpoints = cluster_endpoints(segments, tolerance)
    adjacency = {}
    for idx, (u, v) in enumerate(endpoints):
        adjacency.setdefault(u, []).append(idx)
        adjacency.setdefault(v, []).append(idx)

    unseen = set(range(len(segments)))
    open_components = []

    while unseen:
        seed = next(iter(unseen))
        stack = [seed]
        component = set()
        while stack:
            edge = stack.pop()
            if edge in component:
                continue
            component.add(edge)
            u, v = endpoints[edge]
            for node in (u, v):
                for neighbor in adjacency.get(node, []):
                    if neighbor not in component:
                        stack.append(neighbor)

        unseen -= component
        nodes = set()
        for edge in component:
            nodes.update(endpoints[edge])

        # A simple closed profile has exactly two incident segment ends at
        # every node. This also allows a single closed polyline to be a loop.
        if any(len(adjacency.get(node, [])) != 2 for node in nodes):
            open_components.append([segments[i] for i in component])
            continue

        # Walk the component in connected order.
        first_edge = min(component)
        first_u, first_v = endpoints[first_edge]
        current_node = first_u
        current_edge = first_edge
        ordered = []
        visited = set()

        while current_edge not in visited:
            visited.add(current_edge)
            seg = segments[current_edge]
            u, v = endpoints[current_edge]

            if u == current_node:
                ordered.append(seg)
                current_node = v
            else:
                ordered.append(seg.reversed())
                current_node = u

            candidates = [
                e for e in adjacency[current_node]
                if e in component and e not in visited
            ]
            if not candidates:
                break
            current_edge = candidates[0]

        if len(visited) == len(component) and current_node == first_u:
            loops.append(ordered)
        else:
            open_components.append([segments[i] for i in component])

    return loops, open_components

def is_hole_loop(loop):
    """Return True if loop contains exactly one full-circle arc."""
    if len(loop) != 1:
        return False

    segment = loop[0]

    if segment["type"] != "ARC":
        return False

    start = segment["start"]
    end = segment["end"]

    same_point = (
        abs(start[0] - end[0]) < 0.001 and
        abs(start[1] - end[1]) < 0.001
    )

    full_circle = abs(abs(segment["sweep"]) - 360) < 0.001

    return same_point and full_circle

def extract_holes(loops):
    holes = []

    for loop in loops:
        if is_hole_loop(loop):
            arc = loop[0]

            holes.append({
                "x": arc["center"][0],
                "y": arc["center"][1],
                "diameter": 2 * arc["radius"]
            })

    return holes

def create_hole_table(holes):
    data = [["Hole", "X", "Y", "Diameter"]]

    for i, hole in enumerate(holes, start=1):
        data.append([
            str(i),
            f'{hole["x"]:.3f}',
            f'{hole["y"]:.3f}',
            f'{hole["diameter"]:.3f}'
        ])

    table = Table(data, repeatRows=1)

    table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0),
         colors.HexColor("#263746")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("BACKGROUND", (1, 1), (2, -1),
         colors.HexColor("#BDD7EE")),
        ("GRID", (0, 0), (-1, -1), 0.35, colors.grey),
        ("ALIGN", (0, 0), (-1, -1), "CENTER"),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
    ]))

    return table

def fmt(value, decimals):
    return f"{value:.{decimals}f}"


def make_pdf(pdf_path, dxf_path, loops, open_components, ignored,
             decimals, units_label, tolerance):
    styles = getSampleStyleSheet()
    generation_date = datetime.now().strftime("%A %Y-%m-%d %I:%M:%S %p")
    story = [
        Paragraph(Path(dxf_path).stem, styles["Title"]),
        Paragraph(f"Source: {Path(dxf_path).name}", styles["Normal"]),
        Paragraph(
            f"Units: {units_label} &nbsp;&nbsp; | &nbsp;&nbsp; "
            f"Coordinate precision: {decimals} decimal places "
            f"&nbsp;&nbsp; | &nbsp;&nbsp; Connection tolerance: {tolerance:g}",
            styles["Normal"]
        ),
        Paragraph(
            "Arc direction is given while traveling from the listed start "
            "point to the listed end point. Positive sweep = CCW; negative = CW.",
            styles["BodyText"]
        ),
        Paragraph(f"Generated: {generation_date}", styles["Normal"]),
        Spacer(1, 0.1 * inch)
    ]


    headers = [
        "Seg.", "Type", "Start X", "Start Y", "End X", "End Y",
        "Center X", "Center Y", "Direction"
    ]

    for loop_num, loop in enumerate(loops, 1):
        story.append(Paragraph(f"Closed Loop {loop_num}", styles["Heading2"]))
        data = [headers]
        for i, seg in enumerate(loop, 1):
            if seg.kind == "ARC":
                direction = "CCW" if seg.sweep >= 0 else "CW"
                data.append([
                    str(i), "ARC",
                    fmt(seg.sx, decimals), fmt(seg.sy, decimals),
                    fmt(seg.ex, decimals), fmt(seg.ey, decimals),
                    fmt(seg.cx, decimals), fmt(seg.cy, decimals),
                    f"{direction} ({abs(seg.sweep):.{decimals}f}°)"
                ])
            else:
                data.append([
                    str(i), "LINE",
                    fmt(seg.sx, decimals), fmt(seg.sy, decimals),
                    fmt(seg.ex, decimals), fmt(seg.ey, decimals),
                    "—", "—", "—"
                ])

        table = Table(
            data,
            repeatRows=1,
            colWidths=[0.38*inch, 0.48*inch, 0.76*inch, 0.76*inch,
                       0.76*inch, 0.76*inch, 0.82*inch, 0.82*inch, 1.05*inch]
        )
        table.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#263746")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
            ("FONTSIZE", (0, 0), (-1, -1), 7),
            ("LEADING", (0, 0), (-1, -1), 9),
            ("GRID", (0, 0), (-1, -1), 0.35, colors.grey),
            ("ROWBACKGROUNDS", (0, 1), (-1, -1),
             [colors.white, colors.HexColor("#EEF2F5")]),
            ("ALIGN", (0, 0), (-1, -1), "CENTER"),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("TOPPADDING", (0, 0), (-1, -1), 4),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
            
            # Start X and Y - Green background
            ("BACKGROUND", (2, 1), (3, -1), colors.HexColor("#C6EFCE")),

            # End X and Y - Red background
            ("BACKGROUND", (4, 1), (5, -1), colors.HexColor("#FFC7CE")),
            # End coordinates - Bold
            ("FONTNAME", (4, 1), (5, -1), "Helvetica-Bold"),

            # Center X and Y - Blue background
            ("BACKGROUND", (6, 1), (7, -1), colors.HexColor("#BDD7EE")),
            # Center coordinates - Italic
            ("FONTNAME", (6, 1), (7, -1), "Helvetica-Oblique"),
        ]))
        story.append(table)
        story.append(Spacer(1, 0.22 * inch))

    if open_components:
        story.append(PageBreak())
        story.append(Paragraph("Open / Unjoined Geometry", styles["Heading1"]))
        story.append(Paragraph(
            "These entities did not form closed loops. Check for gaps, "
            "duplicate geometry, branches, or an unsuitable connection tolerance.",
            styles["BodyText"]
        ))
        for comp_num, component in enumerate(open_components, 1):
            story.append(Paragraph(
                f"Open component {comp_num} ({len(component)} segments)",
                styles["Heading2"]
            ))
            data = [headers]
            for i, seg in enumerate(component, 1):
                if seg.kind == "ARC":
                    direction = "CCW" if seg.sweep >= 0 else "CW"
                    row = [
                        str(i), "ARC", fmt(seg.sx, decimals), fmt(seg.sy, decimals),
                        fmt(seg.ex, decimals), fmt(seg.ey, decimals),
                        fmt(seg.cx, decimals), fmt(seg.cy, decimals),
                        f"{direction} ({abs(seg.sweep):.{decimals}f}°)"
                    ]
                else:
                    row = [
                        str(i), "LINE", fmt(seg.sx, decimals), fmt(seg.sy, decimals),
                        fmt(seg.ex, decimals), fmt(seg.ey, decimals),
                        "—", "—", "—"
                    ]
                data.append(row)
            table = Table(data, repeatRows=1)
            table.setStyle(TableStyle([
                ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#5B4636")),
                ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
                ("GRID", (0, 0), (-1, -1), 0.35, colors.grey),
                ("FONTSIZE", (0, 0), (-1, -1), 7),
                ("ALIGN", (0, 0), (-1, -1), "CENTER"),
                
                # Start X and Y - Green background
                ("BACKGROUND", (2, 1), (3, -1), colors.HexColor("#C6EFCE")),

                # End X and Y - Red background
                ("BACKGROUND", (4, 1), (5, -1), colors.HexColor("#FFC7CE")),
                # End coordinates - Bold
                ("FONTNAME", (4, 1), (5, -1), "Helvetica-Bold"),

                # Center X and Y - Blue background
                ("BACKGROUND", (6, 1), (7, -1), colors.HexColor("#BDD7EE")),
                # Center coordinates - Italic
                ("FONTNAME", (6, 1), (7, -1), "Helvetica-Oblique"),
            ]))
            story.append(table)
            story.append(Spacer(1, 0.15 * inch))

    if ignored:
        story.append(Spacer(1, 0.15 * inch))
        ignored_text = ", ".join(f"{k}: {v}" for k, v in sorted(ignored.items()))
        story.append(Paragraph(
            f"Unsupported/ignored entity types in modelspace: {ignored_text}",
            styles["BodyText"]
        ))

    doc = SimpleDocTemplate(
        str(pdf_path), pagesize=portrait(letter),
        rightMargin=0.35*inch, leftMargin=0.35*inch,
        topMargin=0.2*inch, bottomMargin=0.2*inch
    )
    doc.build(story)


def main():
    root = tk.Tk()
    root.withdraw()

    dxf_file = filedialog.askopenfilename(
        title="Select DXF file",
        filetypes=[("DXF files", "*.dxf"), ("All files", "*.*")]
    )
    if not dxf_file:
        return

    tolerance = simpledialog.askfloat(
        "Connection tolerance",
        "Maximum endpoint gap to treat as connected.\n"
        "Use 0.001 for a typical small tolerance (in drawing units):",
        initialvalue=0.001, minvalue=0.0
    )
    if tolerance is None:
        return

    decimals = simpledialog.askinteger(
        "Coordinate precision",
        "Number of decimal places in the PDF:",
        initialvalue=4, minvalue=0, maxvalue=8
    )
    if decimals is None:
        return

    units = simpledialog.askstring(
        "Drawing units",
        "Units label for the PDF (e.g. inches, mm, or drawing units):",
        initialvalue="Drawing units"
    )
    if units is None:
        return

    try:
        doc = ezdxf.readfile(dxf_file)
        segments, circles, ignored = extract_segments(doc)
        loops, open_components = group_loops(segments, circles, tolerance)

        if not loops and not open_components:
            messagebox.showwarning(
                "No geometry found",
                "No supported LINE, ARC, CIRCLE, or 2D polyline geometry was found."
            )
            return

        default_pdf = str(Path(dxf_file).with_suffix("")) + "_coordinates.pdf"
        pdf_file = filedialog.asksaveasfilename(
            title="Save coordinate PDF",
            defaultextension=".pdf",
            initialfile=Path(default_pdf).name,
            filetypes=[("PDF files", "*.pdf")]
        )
        if not pdf_file:
            return

        make_pdf(
            pdf_file, dxf_file, loops, open_components, ignored,
            decimals, units.strip() or "Drawing units", tolerance
        )
        messagebox.showinfo(
            "PDF created",
            f"Saved coordinate sheet:\n{pdf_file}\n\n"
            f"Closed loops: {len(loops)}\n"
            f"Open/unjoined components: {len(open_components)}"
        )

    except Exception as exc:
        messagebox.showerror("DXF processing error", str(exc))


if __name__ == "__main__":
    main()
