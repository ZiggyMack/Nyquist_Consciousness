# Rename all run021 files to run020b

$basePath = "d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA"

# 1. Rename temporal_logs JSON files
$temporalLogs = "$basePath\0_results\temporal_logs"
Get-ChildItem -Path $temporalLogs -Filter "run021_*.json" | ForEach-Object {
    $newName = $_.Name -replace "run021_", "run020b_"
    Rename-Item -Path $_.FullName -NewName $newName
    Write-Host "Renamed: $($_.Name) -> $newName"
}

# 2. Rename runs JSON files
$runsDir = "$basePath\0_results\runs"
Get-ChildItem -Path $runsDir -Filter "S7_run_021_*.json" | ForEach-Object {
    $newName = $_.Name -replace "S7_run_021_", "S7_run_020b_"
    Rename-Item -Path $_.FullName -NewName $newName
    Write-Host "Renamed: $($_.Name) -> $newName"
}

# 3. Rename dryrun files
$dryrunDir = "$runsDir\dryrun"
if (Test-Path $dryrunDir) {
    Get-ChildItem -Path $dryrunDir -Filter "S7_run_021_*.json" | ForEach-Object {
        $newName = $_.Name -replace "S7_run_021_", "S7_run_020b_"
        Rename-Item -Path $_.FullName -NewName $newName
        Write-Host "Renamed (dryrun): $($_.Name) -> $newName"
    }
}

# 4. Rename files inside run020b folder (was run021)
$run020bFolder = "$temporalLogs\run020b"
if (Test-Path $run020bFolder) {
    Get-ChildItem -Path $run020bFolder -Filter "run021_*.json" -Recurse | ForEach-Object {
        $newName = $_.Name -replace "run021_", "run020b_"
        Rename-Item -Path $_.FullName -NewName $newName
        Write-Host "Renamed (run020b folder): $($_.Name) -> $newName"
    }
}

Write-Host "`nDone! All run021 files renamed to run020b."
