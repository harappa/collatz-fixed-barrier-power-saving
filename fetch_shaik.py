#!/usr/bin/env python3
"""Fetch Shaik's formalization (GitHub, Apache-2.0), apply the porting patch, and place it in vendor/shaik.

I. A. Shaik, "Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density": Lean formalization
FirstPassageLinearTransport (commit 7239f88d05d8262d4778f3c46f4560905052872f, Lean v4.15.0).
Only the 25 files of the import closure of FixedBarrier.lean are used. FixedBarrier.lean (the fixed-target
form of Theorem 5.3 of the manuscript, Section 5) was added by this project; it is not part of Shaik's repository.
patches/shaik-v4.30.patch ports the files to Lean v4.30.0-rc2 / Mathlib v4.30.0-rc2 (statements unchanged)
and adds FixedBarrier.lean. The original sources are not redistributed with this bundle.

Verification: the git commit hash, and the SHA-256 of the 25 files after patching. Dependencies: Mathlib only.
"""
import hashlib
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = "https://github.com/shaikidris/FirstPassageLinearTransport"
COMMIT = "7239f88d05d8262d4778f3c46f4560905052872f"
HERE = Path(__file__).resolve().parent
DEST = HERE / "vendor" / "shaik"
PATCH = HERE / "patches" / "shaik-v4.30.patch"

FILES = [
    ("FirstPassageLinearTransport/AdjustableBarrierDensity.lean", "7ecdd54fbe2bfc78cdf4001bc39b51d1062846aa85eef1c9bdc07e2d6063dff8"),
    ("FirstPassageLinearTransport/AdjustableEnvelope.lean", "8e6d97cd6c7bf3dadce34187bf0322391d654eb196c26172736566a569d71421"),
    ("FirstPassageLinearTransport/Barrier.lean", "c9852c5ae35c0c5467e44ece58a6c08875002b76f1ddfff5f8d22cddea50ef88"),
    ("FirstPassageLinearTransport/BarrierDensity.lean", "01e5dc4f4312fbae3d357880e4db9e0eacb634182427b9d249004616145a7807"),
    ("FirstPassageLinearTransport/Basic.lean", "497133aa9e695036c9ce01058673f38df187b81bf5406e47ba5e30c280dcc6a2"),
    ("FirstPassageLinearTransport/Density.lean", "4c4f2fc8f262dc46405be323302d60a570f2e74dee3cd841159d3747549272e6"),
    ("FirstPassageLinearTransport/EntropyBarrier.lean", "0dc241cf132045edf64c683dcf498ab262726e513e9197dbddd22a6a21afdcb7"),
    ("FirstPassageLinearTransport/Envelope.lean", "29403e35383e7403ec3224e4ad0c872e92339107749ada7093f7074732c3c047"),
    ("FirstPassageLinearTransport/FirstBadEnvelope.lean", "aecee211665a91b71a5dc88407d138b2a85cdc12130e4485d5780f222f8deacc"),
    ("FirstPassageLinearTransport/FirstPassage.lean", "8b8f8aae24c859dec3a00e8f2115a7d149e2e96e3a37b8a30ec7e87147367028"),
    ("FirstPassageLinearTransport/FixedBarrier.lean", "f97267a0605fb1dc252330ace259c72d360efa7940549d55bc8d23ea8197cbe3"),
    ("FirstPassageLinearTransport/LossTransport.lean", "6efd1fe61a15e58e0733e789d62d17ef5595fc65f473df1312f5a185fca2d5b0"),
    ("FirstPassageLinearTransport/NestedRecertification.lean", "2f1e54b6fa0f9e5cb2976c5df83bf3fb0bf60054f1b50e3b5e800ebdb707d39a"),
    ("FirstPassageLinearTransport/Parameters.lean", "9b782d53eb457e3594cff7623b47c08629f4def656c3b83f725e1e1ef423415b"),
    ("FirstPassageLinearTransport/Parity.lean", "f14dfe89834489042ba546a9c9ea764592122b7c9f50c8b9141251a2687f5f61"),
    ("FirstPassageLinearTransport/PolylogTerminalSchedule.lean", "fe4f1aa87c1e07e8dddb3dda74550a8ce8065475866fbe88f2acc529d6db69d0"),
    ("FirstPassageLinearTransport/Pullback.lean", "20207e3f47957fb9256b936ee7a8d34ab96f49bfb9cdaed8b203af011f332a10"),
    ("FirstPassageLinearTransport/RankScaledLoss.lean", "9183914f7769a82f2c241ee6b6d4ccdb79a32c8e725c5bf2b795f152c2094636"),
    ("FirstPassageLinearTransport/RawDynamics.lean", "027a7581a3fa7dcca732600d6de16b8181496b8609c9345e5fd0f02be93f74c7"),
    ("FirstPassageLinearTransport/RecertificationRun.lean", "d3028c958fae11c7916c1465169acc10a03c2ee1f51dae1605b9962ced4aca41"),
    ("FirstPassageLinearTransport/RecertificationStep.lean", "7cd68a8d07def8409b06696a37b8cf970edcea43bb5b02fcf2235d0eb315f54c"),
    ("FirstPassageLinearTransport/TerminalProfile.lean", "85ae033ff3e0f4a63e9b65c9c222b1f42d0e37918f4372bd381c16d9661d5449"),
    ("FirstPassageLinearTransport/TerminalTail.lean", "83364297319a712cdc9f89f37f3ad308e698744360616195e7937971605b27e8"),
    ("FirstPassageLinearTransport/TerminalTailAsymptotics.lean", "47b96178b86826c141ca0e381482cb32b113cdf64ab9d296e52ea2d51a19e1b9"),
    ("FirstPassageLinearTransport/Transport.lean", "4497a18f3f50c1ad2c55c394eeb22069fd8716d7ad17c98c10975bb829b48c56"),
]


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        t = Path(tmp)
        subprocess.run(["git", "init", "-q", str(t)], check=True)
        subprocess.run(["git", "-C", str(t), "fetch", "-q", "--depth", "1", REPO, COMMIT], check=True)
        subprocess.run(["git", "-C", str(t), "checkout", "-q", "FETCH_HEAD"], check=True)
        head = subprocess.run(["git", "-C", str(t), "rev-parse", "HEAD"], check=True,
                              capture_output=True, text=True).stdout.strip()
        if head != COMMIT:
            print(f"commit mismatch: {head}", file=sys.stderr)
            return 1
        if DEST.exists():
            shutil.rmtree(DEST)
        (DEST / "FirstPassageLinearTransport").mkdir(parents=True)
        shutil.copy(t / "LICENSE", DEST / "LICENSE")
        for rel, _ in FILES:
            src = t / "lean" / rel
            if src.exists():
                dst = DEST / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(src, dst)
    with open(PATCH, "rb") as f:
        subprocess.run(["patch", "-s", "-p1", "--no-backup-if-mismatch", "-d", str(DEST)], stdin=f, check=True)
    bad = [rel for rel, h in FILES if not (DEST / rel).exists() or sha256(DEST / rel) != h]
    if bad:
        print("SHA-256 mismatch: " + ", ".join(bad), file=sys.stderr)
        return 1
    print(f"verified: commit {COMMIT[:7]}, {len(FILES)} files after patching -> {DEST}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
