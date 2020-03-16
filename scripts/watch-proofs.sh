#!/usr/bin/env bash
watch -n 2 "bash -c 'pgrep python | xargs ps -fp | grep \"solver.py --\" | grep \$USER'"
