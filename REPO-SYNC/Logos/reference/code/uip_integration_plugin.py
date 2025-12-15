"""Stub UIP integration plugin."""

from __future__ import annotations


def available() -> bool:
    return False


def get_uip_integration_plugin() -> dict[str, object]:
    return {"available": available(), "mode": "stub"}


def initialize_uip_integration() -> dict[str, object]:
    return get_uip_integration_plugin()
