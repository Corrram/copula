@echo off
rem Builds the draft modules and writes everything to build-draft.log in the repo root.
set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
cd /d "%~dp0.."
where lake >nul 2>nul
if errorlevel 1 (
  echo lake not found. Install elan first: https://leanprover-community.github.io/get_started.html > build-draft.log
  exit /b 1
)
lake exe cache get > build-draft.log 2>&1
lake build Copula.Draft >> build-draft.log 2>&1
echo lake build exit code: %errorlevel% >> build-draft.log
