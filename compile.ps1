# LogicK 一键编译脚本
# 按 _CoqProject 中的依赖顺序编译所有 .v 文件

$ErrorActionPreference = "Stop"
$files = Get-Content "$PSScriptRoot\_CoqProject" | Where-Object { $_ -match '\.v$' -and $_ -notmatch '^\s*#' }

$total = $files.Count
$ok = 0

foreach ($f in $files) {
    Write-Host "[$($ok+1)/$total] $f" -ForegroundColor Cyan
    coqc "$PSScriptRoot\$f"
    if ($LASTEXITCODE -ne 0) {
        Write-Host "ERROR: $f 编译失败" -ForegroundColor Red
        exit 1
    }
    $ok++
}

Write-Host "`n全部 $total 个文件编译通过!" -ForegroundColor Green
