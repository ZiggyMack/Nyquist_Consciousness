# CFA Trinity v3 - Overnight Biocentrism Batch
# Target: All 8 B-stances x 2 conditions (external + control) x 5 runs = 80 runs
# Rationale: B stances have 10-11 runs each vs 40-82 for all others

$ErrorActionPreference = "Continue"
Set-Location "D:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\12_CFA"

$logFile = "D:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\12_CFA\overnight_batch_log.txt"

$stances = @("b_vs_ct", "b_vs_mdn", "b_vs_pt", "b_vs_g", "ct_vs_b", "mdn_vs_b", "pt_vs_b", "g_vs_b")
$runsPerStancePerCondition = 5
$total = $stances.Count * 2 * $runsPerStancePerCondition
$completed = 0
$failed = 0

$startTime = Get-Date
"BATCH START: $startTime" | Out-File -FilePath $logFile -Encoding utf8
"Stances: $($stances -join ', ')" | Out-File -FilePath $logFile -Append -Encoding utf8
"Runs per stance per condition: $runsPerStancePerCondition" | Out-File -FilePath $logFile -Append -Encoding utf8
"Total planned: $total" | Out-File -FilePath $logFile -Append -Encoding utf8
"" | Out-File -FilePath $logFile -Append -Encoding utf8

Write-Host "CFA OVERNIGHT BATCH STARTED - $total runs planned"

foreach ($stance in $stances) {
    foreach ($condition in @("external", "control")) {
        for ($run = 1; $run -le $runsPerStancePerCondition; $run++) {
            $runNum = $completed + $failed + 1
            $msg = "[$runNum/$total] $stance | $condition | run $run"
            Write-Host $msg
            $msg | Out-File -FilePath $logFile -Append -Encoding utf8

            if ($condition -eq "external") {
                $output = python run_cfa_trinity_v3.py --stance $stance --external-identities 2>&1
            } else {
                $output = python run_cfa_trinity_v3.py --stance $stance --control 2>&1
            }

            $exitCode = $LASTEXITCODE
            $output | Out-File -FilePath $logFile -Append -Encoding utf8

            if ($exitCode -eq 0) {
                $completed++
                $status = "[OK] $completed done so far - $stance $condition"
            } else {
                $failed++
                $status = "[FAIL] $stance $condition - continuing"
            }

            Write-Host $status
            $status | Out-File -FilePath $logFile -Append -Encoding utf8

            Start-Sleep -Seconds 5
        }
    }
}

$endTime = Get-Date
"" | Out-File -FilePath $logFile -Append -Encoding utf8
"BATCH COMPLETE" | Out-File -FilePath $logFile -Append -Encoding utf8
"Completed: $completed" | Out-File -FilePath $logFile -Append -Encoding utf8
"Failed: $failed" | Out-File -FilePath $logFile -Append -Encoding utf8
"Finished: $endTime" | Out-File -FilePath $logFile -Append -Encoding utf8

Write-Host "BATCH COMPLETE - $completed done, $failed failed"
