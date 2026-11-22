for u in ["https://example.com/a", "/relative", "javascript:alert(1)", "data:text/html,x", "blob:https://x/1", "file:///etc/passwd", "intent://x#Intent;end", "http://example.com", "https://", "HTTPS://example.com/", "https://user@example.com/", "mailto:a@b.c", "nostr:npub1x"] {
  print(u, "->", LinkUrl.error(u) ?? "OK")
}
