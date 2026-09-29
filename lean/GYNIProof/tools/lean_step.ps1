param(
  [Parameter(Mandatory = $true)][string]$File,      # e.g. GYNIProof/Core.lean (relative to formal-conjectures/)
  [string]$Olean = "",                              # e.g. .lake/build/lib/lean/GYNIProof/Core.olean ("" = no output)
  [int]$PeakMB = 3400,                              # expected peak WORKING SET of this Lean process (MB)
  [int]$ReserveMB = 1536,                           # required headroom on top of the expected peak (MB)
  [int]$PollSec = 60
)
# RAM rules (GYNIProof/LOG.md): before starting, wait until (a) no lean.exe is running and
# (b) Available MBytes >= PeakMB + ReserveMB (expected peak working set + 1.5 GB); poll every
# PollSec seconds. Then run `lake env lean` (one process) and report the exit code, wall time,
# peak working set and peak private bytes. If the process dies without any Lean error message
# (e.g. killed by the machine's out-of-memory guard), wait 2 minutes and retry once.
$ErrorActionPreference = "Stop"
$root = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)   # formal-conjectures/
$need = $PeakMB + $ReserveMB
$env:PATH = "$env:USERPROFILE\.elan\bin;" + $env:PATH
$argl = @("env", "lean")
if ($Olean -ne "") {
  New-Item -ItemType Directory -Force -Path (Join-Path $root (Split-Path -Parent $Olean)) | Out-Null
  $argl += @("-o", $Olean, "-i", ($Olean -replace "\.olean$", ".ilean"))
}
$argl += @($File)
$code = 1
for ($attempt = 1; $attempt -le 2; $attempt++) {
  while ($true) {
    $others = @(Get-Process lean -ErrorAction SilentlyContinue)
    $avail = [int](Get-Counter '\Memory\Available MBytes').CounterSamples.CookedValue
    if ($others.Count -eq 0 -and $avail -ge $need) { break }
    Write-Output ("   [{0}] waiting: other lean.exe = {1}, Available = {2} MB, need {3} MB" -f (Get-Date -Format HH:mm:ss), $others.Count, $avail, $need)
    Start-Sleep -Seconds $PollSec
  }
  $tmpOut = [System.IO.Path]::GetTempFileName()
  $tmpErr = [System.IO.Path]::GetTempFileName()
  $sw = [Diagnostics.Stopwatch]::StartNew()
  $p = Start-Process -FilePath "lake" -ArgumentList $argl -WorkingDirectory $root -NoNewWindow -PassThru `
    -RedirectStandardOutput $tmpOut -RedirectStandardError $tmpErr
  $null = $p.Handle
  $peakWS = 0; $peakPriv = 0
  while (-not $p.HasExited) {
    Start-Sleep -Milliseconds 500
    # no other lean.exe was running at the start (see above), so every lean.exe now is ours
    foreach ($k in @(Get-Process lean -ErrorAction SilentlyContinue)) {
      try {
        $k.Refresh()
        if ($k.PeakWorkingSet64 -gt $peakWS) { $peakWS = $k.PeakWorkingSet64 }
        if ($k.WorkingSet64 -gt $peakWS) { $peakWS = $k.WorkingSet64 }
        if ($k.PrivateMemorySize64 -gt $peakPriv) { $peakPriv = $k.PrivateMemorySize64 }
      } catch { }
    }
  }
  $p.WaitForExit()
  $sw.Stop()
  $out = @(Get-Content $tmpOut) + @(Get-Content $tmpErr)
  Remove-Item $tmpOut, $tmpErr -ErrorAction SilentlyContinue
  $out
  $code = $p.ExitCode
  Write-Output ("   RESULT {0}: exit={1} wall={2:N1}s peakWS={3:N0}MB peakPrivate={4:N0}MB (attempt {5})" -f $File, $code, $sw.Elapsed.TotalSeconds, ($peakWS / 1MB), ($peakPriv / 1MB), $attempt)
  $leanError = @($out | Where-Object { $_ -match "error" }).Count -gt 0
  if ($code -eq 0 -or $leanError -or $attempt -eq 2) { break }
  Write-Output "   process ended without a Lean error (killed?): waiting 2 minutes, then retrying once"
  Start-Sleep -Seconds 120
}
exit $code
