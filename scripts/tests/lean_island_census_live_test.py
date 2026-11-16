#!/usr/bin/env python3
"""Aggregate entry point for seven mocks, not the 20 actual compiler probes.

Live controls require lean_island_census_live.py --trustc PATH --out NEW_PATH.
"""

import unittest

from lean_island_census_live import MockProcessControls


if __name__ == "__main__":
    unittest.main()
