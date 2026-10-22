"""make_figures.py -- figures of the manuscript (run: python make_figures.py; writes fig1..fig4 as PDF and PNG).

All numbers are copied from the verified outputs of the certificates (see ../../logs and ../../README.md).
Decimals are directed-rounded: lower bounds down, upper bounds up."""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Arc

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 8, "axes.linewidth": 0.6,
                     "pdf.fonttype": 42, "savefig.dpi": 300})
BLUE, ORANGE, GREY, GREEN, RED = "#1f5aa6", "#d9822b", "#7a7a7a", "#2e8b57", "#b03a2e"


def save(fig, name):
    fig.savefig(name + ".pdf", bbox_inches="tight")
    fig.savefig(name + ".png", bbox_inches="tight")
    plt.close(fig)


def fig1():
    """The GYNI game played with a process matrix."""
    fig, ax = plt.subplots(figsize=(3.5, 2.3))
    ax.set_xlim(0, 10); ax.set_ylim(0, 6.4); ax.axis("off")
    ax.add_patch(FancyBboxPatch((3.0, 0.3), 4.0, 1.3, boxstyle="round,pad=0.12", fc="#e8eef8", ec=BLUE, lw=1.0))
    ax.text(5.0, 0.95, "process matrix $W$\n(no global causal order)", ha="center", va="center",
            fontsize=7.5, color=BLUE)
    for cx, name, inp, out, ilab, olab, side in ((1.9, "Alice", "x", "a", "$A_I$", "$A_O$", +1),
                                                 (8.1, "Bob", "y", "b", "$B_I$", "$B_O$", -1)):
        ax.add_patch(FancyBboxPatch((cx - 1.1, 2.6), 2.2, 1.5, boxstyle="round,pad=0.1", fc="white",
                                    ec="black", lw=0.8))
        ax.text(cx, 3.35, name, ha="center", va="center", fontsize=8.5, weight="bold")
        ax.annotate("", xy=(cx, 4.22), xytext=(cx, 5.3), arrowprops=dict(arrowstyle="->", lw=0.8))
        ax.text(cx, 5.55, "input $" + inp + "\\in\\{0,1\\}$", ha="center", fontsize=7.5)
        ax.annotate("", xy=(cx + side * 1.85, 4.75), xytext=(cx + side * 1.15, 3.95),
                    arrowprops=dict(arrowstyle="->", lw=0.8))
        ax.text(cx + side * 2.05, 4.9, "output $" + out + "$", ha="center", fontsize=7.5)
        ax.add_patch(FancyArrowPatch((cx - 0.45, 1.75), (cx - 0.45, 2.55), arrowstyle="->", lw=0.8,
                                     mutation_scale=7, color=BLUE))
        ax.add_patch(FancyArrowPatch((cx + 0.45, 2.55), (cx + 0.45, 1.75), arrowstyle="->", lw=0.8,
                                     mutation_scale=7, color=BLUE))
        ax.text(cx - 0.6, 2.12, ilab, ha="right", va="center", fontsize=7, color=BLUE)
        ax.text(cx + 0.6, 2.12, olab, ha="left", va="center", fontsize=7, color=BLUE)
    ax.text(5.0, 3.35, "win if $a=y$\nand $b=x$", ha="center", va="center", fontsize=7.5, color=RED)
    save(fig, "fig1_gyni_game")


def fig2():
    """Certified upper bounds versus hierarchy level and explicit lower bounds versus number of blocks."""
    L = np.array([2, 3, 4, 5, 6, 7, 8])
    up = np.array([0.6434871, 0.6267932, 0.6233558, 0.6224213, 0.6222569, 0.6222199, 0.622183755532])
    J = np.array([1, 2, 3, 4])
    lo = np.array([0.6067, 0.621789802, 0.622146712690, 0.622165901353])
    fig, axs = plt.subplots(1, 2, figsize=(7.0, 2.6), gridspec_kw=dict(width_ratios=[1.0, 1.15], wspace=0.32))
    ax = axs[0]
    ax.axhspan(0.6219, 0.7592, color="#eeeeee", zorder=0)
    ax.text(5.2, 0.712, "previously known\ninterval [0.6219, 0.7592]", ha="center", va="top", fontsize=7,
            color=GREY)
    ax.plot(L, up, "v-", color=BLUE, ms=4, lw=1, label="certified upper bound, level $L$")
    ax.plot([1], [0.7462629], "v", mfc="white", color=BLUE, ms=4, label="level 1 (numerical)")
    ax.plot(J, lo, "^-", color=ORANGE, ms=4, lw=1, label="explicit strategy, $J$ blocks")
    ax.axhline(0.5, color="black", lw=0.6, ls=":")
    ax.text(0.75, 0.505, "causal bound 1/2", ha="left", va="bottom", fontsize=7)
    ax.set_xlabel("hierarchy level $L$ / number of blocks $J$")
    ax.set_ylabel("GYNI success probability")
    ax.set_xlim(0.6, 8.4); ax.set_ylim(0.48, 0.77); ax.set_xticks(range(1, 9))
    ax.legend(loc="lower right", fontsize=6.3, frameon=False, bbox_to_anchor=(1.0, 0.1))
    ax.text(-0.17, 1.0, "a", transform=ax.transAxes, fontsize=10, weight="bold")
    ax = axs[1]
    ax.axhspan(0.622165901353, 0.622183755532, color="#f6e7d3", zorder=0)
    ax.plot(L[2:], up[2:], "v-", color=BLUE, ms=4, lw=1)
    ax.plot(J[1:], lo[1:], "^-", color=ORANGE, ms=4, lw=1)
    ax.text(6.4, 0.62198, "$0.622165901353 \\leq I^{\\max}_{\\mathrm{GYNI}}$\n$\\leq 0.622183755532$",
            ha="center", va="center", fontsize=7)
    ax.set_xlabel("hierarchy level $L$ / number of blocks $J$")
    ax.set_xlim(1.6, 8.4); ax.set_ylim(0.62176, 0.62240); ax.set_xticks(range(2, 9))
    ax.ticklabel_format(axis="y", useOffset=False)
    ax.text(-0.32, 1.0, "b", transform=ax.transAxes, fontsize=10, weight="bold")
    save(fig, "fig2_bounds")


def fig3():
    """How the two bounds are established."""
    fig, ax = plt.subplots(figsize=(7.0, 1.95)); ax.axis("off"); ax.set_xlim(0, 20); ax.set_ylim(0, 5)
    boxes = [
        (0.2, 2.8, "Lüders normal form\n+ moment hierarchy\n(soundness theorem)", BLUE),
        (5.2, 2.8, "numerical SDP at level 8\n(167,620 variables,\n789,678 constraints)", GREY),
        (10.2, 2.8, "rational dual certificate\n(multipliers in $2^{-50}\\mathbb{Z}$)", BLUE),
        (15.2, 2.8, "exact positivity check of\nfour 289 x 289 blocks\n(integer arithmetic)", GREEN),
        (5.2, 0.2, "explicit J = 4 strategy\n(rational 16384 x 16384\nprocess matrix)", ORANGE),
        (10.2, 0.2, "exact checks: validity,\n676 positive definite\nblocks, exact value", GREEN),
        (15.2, 0.2, "Lean 4 + Mathlib:\nboth bounds checked\nby the proof kernel", RED),
    ]
    for x, y, txt, c in boxes:
        ax.add_patch(FancyBboxPatch((x, y), 4.4, 1.9, boxstyle="round,pad=0.1", fc="white", ec=c, lw=1.0))
        ax.text(x + 2.2, y + 0.95, txt, ha="center", va="center", fontsize=6.5)
    for (x0, y0, x1, y1) in ((4.75, 3.75, 5.1, 3.75), (9.75, 3.75, 10.1, 3.75), (14.75, 3.75, 15.1, 3.75),
                             (9.75, 1.15, 10.1, 1.15), (14.75, 1.15, 15.1, 1.15), (17.4, 2.7, 17.4, 2.25)):
        ax.annotate("", xy=(x1, y1), xytext=(x0, y0), arrowprops=dict(arrowstyle="->", lw=0.9))
    ax.text(2.4, 1.15, "upper bound: top row\nlower bound: bottom row", ha="center", va="center", fontsize=6.6)
    save(fig, "fig3_verification")


def fig4():
    """The J = 4 strategy: measurement directions in the four Jordan blocks."""
    t = np.array([9.59850, 34.42477, 51.18469, 84.13806])
    cols = ["#1f5aa6", "#2e8b57", "#d9822b", "#b03a2e"]
    fig = plt.figure(figsize=(3.5, 2.4))
    ax = fig.add_axes([0.0, 0.05, 0.6, 0.95]); ax.set_aspect("equal"); ax.axis("off")
    ax.add_patch(Arc((0, 0), 2.0, 2.0, theta1=0, theta2=180, lw=0.6, color=GREY))
    for tj, c, k in zip(t, cols, range(1, 5)):
        th = np.deg2rad(tj)
        for s, ls in ((+1, "-"), (-1, "--")):
            ax.annotate("", xy=(np.sin(s * th / 2), np.cos(s * th / 2)), xytext=(0, 0),
                        arrowprops=dict(arrowstyle="->", color=c, lw=1.0, ls=ls))
    ax.set_xlim(-1.25, 1.45); ax.set_ylim(-0.3, 1.3)
    ax.text(-1.2, 1.2, "a", fontsize=10, weight="bold")
    ax.text(0.1, -0.12, "measurement vectors per block\n(solid: $x=1$; dashed: $x=0$;\ncolours as in b)",
            ha="center", va="top", fontsize=6.5)
    ax2 = fig.add_axes([0.70, 0.2, 0.28, 0.7])
    ax2.barh(range(4), t, color=cols, height=0.6)
    ax2.set_yticks(range(4)); ax2.set_yticklabels([f"$t_{k}$" for k in range(1, 5)]); ax2.invert_yaxis()
    ax2.set_xlabel("angle (degrees)"); ax2.set_xlim(0, 100)
    for k, v in enumerate(t):
        ax2.text(v + 2, k, f"{v:.1f}", va="center", fontsize=6.5)
    ax2.text(-0.5, 1.06, "b", transform=ax2.transAxes, fontsize=10, weight="bold")
    save(fig, "fig4_strategy")


if __name__ == "__main__":
    fig1(); fig2(); fig3(); fig4()
    print("figures written")
