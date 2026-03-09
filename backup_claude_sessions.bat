@echo off
REM ============================================================================
REM Claude Code Session Backup Script (Windows)
REM ============================================================================
REM Copies all session JSONL transcript files from Claude Code's storage to a
REM safe location inside the repo. Prevents loss from VSCode extension updates.
REM
REM Usage:  double-click this file, or run from command prompt
REM ============================================================================

setlocal enabledelayedexpansion

set "SOURCE_DIR=%USERPROFILE%\.claude\projects\d--Documents-Nyquist-Consciousness"
set "BACKUP_DIR=d:\Documents\Nyquist_Consciousness\.claude-session-backups"

if not exist "%BACKUP_DIR%" mkdir "%BACKUP_DIR%"

echo === Claude Session Backup ===
echo Source: %SOURCE_DIR%
echo Backup: %BACKUP_DIR%
echo.

set copied=0
set skipped=0

for %%F in ("%SOURCE_DIR%\*.jsonl") do (
    set "filename=%%~nxF"
    set "dest=%BACKUP_DIR%\%%~nxF"

    REM Use xcopy /D to only copy if source is newer
    xcopy "%%F" "%BACKUP_DIR%\" /D /Y /Q >nul 2>&1
    if !errorlevel! == 0 (
        echo [COPIED] %%~nxF
        set /a copied+=1
    ) else (
        echo [SKIP]   %%~nxF - backup is current
        set /a skipped+=1
    )
)

echo.
echo Done. Copied: %copied%, Skipped: %skipped%
echo Backups stored in: %BACKUP_DIR%
pause
