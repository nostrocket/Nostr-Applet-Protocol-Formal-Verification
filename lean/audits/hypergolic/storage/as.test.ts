import test from 'node:test';
import {captureConfigSchema} from '/Users/gareth/git/napplets/hypergolic/src/presentation/config-schema.ts';
test('a',()=>{try{captureConfigSchema({type:'object',properties:{list:{type:'array',items:{type:'string','x-napplet-secret':true},default:['public-default']}}});console.log('AS accepted');}catch(e:any){console.log('AS rejected',e.code);}});
