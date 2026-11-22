import { parse } from 'parse5';
const { build, csp } = await import(process.argv[2]);
const vectors = [
  "", "<!DOCTYPE html><html><head><title>x</title></head></html>",
  "<!doctype HTML>\n<HTML LANG=en>\n <HEAD>\n<TITLE>x</TITLE>", "﻿<!doctype html><head>",
  "<title>x</title><script>NAPMARK()</script>", "<script>NAPMARK()</script><head></head>",
  "<meta charset=utf-8><head>", "<base href=https://evil.example/><head>",
  "<!-- x --!><script>NAPMARK()</script><head>", "<!--><script>NAPMARK()</script>", "<!---><script>NAPMARK()</script>",
  "<!-- a -- > b --><head>", "<!--<!-- x --><head>",
  "<html data-x=\"><script>NAPMARK()</script>\"><head>", "<html data-x='>'><HEAD data-y=\">\">",
  "<!-- never closed <script>NAPMARK()</script>", "<html lang=\"en", "<head lang=\"en",
  "<?xml version=\"1.0\"?><!x><head>", "</><head>", "</p><head>", "hi<head>", "< head>",
  "<!DOCTYPE html PUBLIC \"-//W3C//DTD>\" \"x\"><head>", "<HEAD/>",
  // same adversarial heads behind a doctype, the only shape Hypergolic admits
  "<!doctype html><html><!-- x --!><script>NAPMARK()</script><head>",
  "<!doctype html><html><!--><script>NAPMARK()</script><head>",
  "<!doctype html><html><head><script>NAPMARK()</script>",
  "<!doctype html><html data-x=\"><script>NAPMARK()</script>\"><head>",
  "<!doctype html><html><head data-y=\">\"><script>NAPMARK()</script>",
  "<!doctype html><html><!-- a -- > b --><head><script>NAPMARK()</script>",
];
function walk(n, out) { if (n.tagName) out.push(n); for (const c of n.childNodes ?? []) walk(c, out); if (n.content) walk(n.content, out); return out; }
const text = n => (n.childNodes ?? []).map(c => c.value ?? '').join('');
let accepted = 0, rejected = 0, violations = 0;
for (const v of vectors) {
  let out;
  try { out = build(v); } catch (e) { rejected++; console.log(`REJECT  ${JSON.stringify(v)}  (${e.message})`); continue; }
  accepted++;
  const doc = parse(out);
  const els = walk(doc, []).filter(e => !['html', 'head', 'body'].includes(e.tagName));
  const head = walk(doc, []).find(e => e.tagName === 'head');
  const firstHeadEl = head.childNodes.find(c => c.tagName);
  const cspOk = firstHeadEl?.tagName === 'meta' && firstHeadEl.attrs.find(a => a.name === 'content')?.value === csp && els[0] === firstHeadEl;
  const scripts = els.filter(e => e.tagName === 'script');
  const preludeIdx = scripts.findIndex(s => s.attrs.some(a => a.name === 'data-kehto-nip5d-injection'));
  const napIdx = scripts.findIndex(s => text(s).includes('NAPMARK()'));
  const bootOk = preludeIdx >= 0 && (napIdx < 0 || preludeIdx < napIdx) && scripts.slice(0, preludeIdx).every(s => !text(s).includes('NAPMARK()'));
  const ok = cspOk && bootOk;
  if (!ok) violations++;
  console.log(`${ok ? 'OK    ' : 'VIOLATE'} ${JSON.stringify(v)}  csp_first=${cspOk} bootstrap_first=${bootOk}`);
}
console.log(`accepted=${accepted} rejected=${rejected} violations=${violations}`);
