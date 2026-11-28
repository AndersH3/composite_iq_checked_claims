"""Backwards-compatible import facade for the centralized report statistics.

Canonical implementation: library.python.statistics. Do not add computations
here; Hoeflin/Ferguson, Towers and Sequential statistics share the same code.
"""
from library.python.statistics import (
    HOEFLIN, TOWERS, SEQUENTIAL, PROJECTS, COMMON, MOMENT_META, EVENT_META,
    moment_result, event_result, pool_rows,
)

# Explicitly preserve the historical public API. These imports are
# intentional re-exports, not unused implementations.
__all__ = [
    "HOEFLIN",
    "TOWERS",
    "SEQUENTIAL",
    "PROJECTS",
    "COMMON",
    "MOMENT_META",
    "EVENT_META",
    "moment_result",
    "event_result",
    "pool_rows",
]
