const { build } = await import(process.argv[2]);
const t = (label, v) => { try { build(v); console.log(label, 'ACCEPT'); } catch (e) { console.log(label, 'REJECT', e.message); } };
const dec = b => new TextDecoder('utf-8', { fatal: true }).decode(b);
const enc = s => new TextEncoder().encode(s);
t('bom-vector raw              ', '﻿<!doctype html><head>');
t('bom-vector after TextDecoder', dec(enc('﻿<!doctype html><head>')));
t('bom+valid raw               ', '﻿<!doctype html><html><head></head><body></body></html>');
t('bom+valid after TextDecoder ', dec(enc('﻿<!doctype html><html><head></head><body></body></html>')));
