#!/bin/bash
lctl set_param osc.*.max_pages_per_rpc=16M
lctl set_param osc.*.max_rpcs_in_flight=8
lctl set_param osc.*.max_dirty_mb=512
lctl set_param llite.*.max_read_ahead_mb=2048
