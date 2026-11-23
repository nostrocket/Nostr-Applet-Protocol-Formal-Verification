"""Verify the Relay query fixture with the Bitcoin BIP-340 reference implementation."""

import hashlib
import json
import runpy
import sys
from pathlib import Path


def main(verifier, trace):
    steps = [json.loads(line) for line in Path(trace).read_text(encoding="utf-8").splitlines()]
    (event,) = (step["reply"]["event"] for step in steps if step.get("reply", {}).get("t") == "event")
    (query,) = (step["msg"] for step in steps if step.get("msg", {}).get("type") == "relay.query")
    expected_filter = {"authors": [event["pubkey"]], "kinds": [event["kind"]], "limit": 1}
    if query["filters"] != [expected_filter]:
        raise SystemExit("Relay fixture event does not match the expected single-author query")

    payload = [0, event["pubkey"], event["created_at"], event["kind"], event["tags"], event["content"]]
    serialized = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    digest = hashlib.sha256(serialized).digest()
    if digest.hex() != event["id"]:
        raise SystemExit("Relay fixture has an invalid NIP-01 event ID")
    verify = runpy.run_path(verifier)["schnorr_verify"]
    if not verify(digest, bytes.fromhex(event["pubkey"]), bytes.fromhex(event["sig"])):
        raise SystemExit("Relay fixture has an invalid BIP-340 signature")
    print("Signed Relay query fixture verified")


if __name__ == "__main__":
    main(*sys.argv[1:])
