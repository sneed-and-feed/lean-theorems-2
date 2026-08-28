$ErrorActionPreference = "Stop"
$root = (Get-Item $PSScriptRoot).Parent.FullName

$theorems = @(
    "alon_boppana",
    "mengers_theorem",
    "macmahons_master_theorem",
    "colorful_caratheodory",
    "blichfeldts_theorem",
    "hoffman_singleton",
    "rsk_bijection",
    "birkhoff_von_neumann",
    "stanley_sl2"
)

$results = @()

foreach ($t in $theorems) {
    Write-Host "`n>>> RUNNING AUDIT FOR $t <<<" -ForegroundColor Yellow
    & powershell -ExecutionPolicy Bypass -File "$root\palomar\audit.ps1" $t
    if ($LASTEXITCODE -eq 0) {
        Write-Host ">>> AUDIT PASSED FOR $t <<<" -ForegroundColor Green
        $results += [PSCustomObject]@{ Slug = $t; Status = "PASS" }
    } else {
        Write-Host ">>> AUDIT FAILED FOR $t <<<" -ForegroundColor Red
        $results += [PSCustomObject]@{ Slug = $t; Status = "FAIL" }
        exit 1
    }
}

Write-Host "`n====================================================" -ForegroundColor Cyan
Write-Host "  ALL REMAINING THEOREMS AUDITED SUCCESSFULLY!" -ForegroundColor Cyan
Write-Host "====================================================" -ForegroundColor Cyan
$results | Format-Table -AutoSize
