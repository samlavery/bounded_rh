#!/usr/bin/env bash
# private spec check + stage of the safe-cut AT7c copy (bbaudit), against the live record 67342981/10^8
cd ~/work/riemann-submission/bench
bash pyr/private_check_rec.sh window/bbaudit/AT7cS.lean CandAT7cS 6734302 10000000 67342981 100000000 specroot_at7cs
echo "== stage"
bash nanoda/stage.sh CandAT7cS $PWD/specroot_at7cs
