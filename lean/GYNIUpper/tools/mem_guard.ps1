param([int]$LimitMB = 5500, [int]$Seconds = 900)
# Stops any lean.exe whose working set exceeds LimitMB (safety net while one Lean process runs).
$t0 = Get-Date
while (((Get-Date) - $t0).TotalSeconds -lt $Seconds) {
  foreach ($p in @(Get-Process lean -ErrorAction SilentlyContinue)) {
    if ($p.WorkingSet64 -gt ($LimitMB * 1MB)) {
      Write-Output ("[mem_guard] stopping lean.exe {0} at {1:N0} MB" -f $p.Id, ($p.WorkingSet64 / 1MB))
      Stop-Process -Id $p.Id -Force
    }
  }
  Start-Sleep -Milliseconds 500
}
