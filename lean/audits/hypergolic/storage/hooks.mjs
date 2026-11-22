export async function resolve(spec, ctx, next) {
  try { return await next(spec, ctx); } catch (e) {
    if ((spec.startsWith('.') || spec.startsWith('/')) && !spec.endsWith('.ts')) { try { return await next(spec + '.ts', ctx); } catch {} }
    throw e;
  }
}
