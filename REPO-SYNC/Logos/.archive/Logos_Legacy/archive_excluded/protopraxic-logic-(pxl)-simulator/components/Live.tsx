
import React, { useState, useRef, useEffect } from 'react';
import { GoogleGenAI, LiveSession, Modality, LiveServerMessage } from '@google/genai';
import { decode, decodeAudioData, createBlob } from '../utils/audio';
import MicrophoneIcon from './icons/MicrophoneIcon';
import StopIcon from './icons/StopIcon';
import ShieldExclamationIcon from './icons/ShieldExclamationIcon';

type Status = 'idle' | 'connecting' | 'listening' | 'error';

interface LiveProps {
  agentIdentity: string | null;
}

const Live: React.FC<LiveProps> = ({ agentIdentity }) => {
    const [status, setStatus] = useState<Status>('idle');
    const [error, setError] = useState<string | null>(null);

    const sessionPromiseRef = useRef<Promise<LiveSession> | null>(null);
    const inputAudioContextRef = useRef<AudioContext | null>(null);
    const outputAudioContextRef = useRef<AudioContext | null>(null);
    const mediaStreamRef = useRef<MediaStream | null>(null);
    const scriptProcessorRef = useRef<ScriptProcessorNode | null>(null);
    const mediaStreamSourceRef = useRef<MediaStreamAudioSourceNode | null>(null);
    
    const nextStartTimeRef = useRef(0);
    const sourcesRef = useRef<Set<AudioBufferSourceNode>>(new Set());

    const cleanup = () => {
        scriptProcessorRef.current?.disconnect();
        mediaStreamSourceRef.current?.disconnect();
        mediaStreamRef.current?.getTracks().forEach(track => track.stop());
        inputAudioContextRef.current?.close().catch(console.error);
        outputAudioContextRef.current?.close().catch(console.error);

        scriptProcessorRef.current = null;
        mediaStreamSourceRef.current = null;
        mediaStreamRef.current = null;
        inputAudioContextRef.current = null;
        outputAudioContextRef.current = null;
        sessionPromiseRef.current = null;
        
        sourcesRef.current.forEach(source => {
          try {
            source.stop();
          } catch(e) {
            // may already be stopped
          }
        });
        sourcesRef.current.clear();
        nextStartTimeRef.current = 0;
    };

    const handleStart = async () => {
        if (!agentIdentity) return;
        setError(null);
        setStatus('connecting');

        try {
            const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
            mediaStreamRef.current = stream;
            
            const ai = new GoogleGenAI({ apiKey: process.env.API_KEY });

            inputAudioContextRef.current = new (window.AudioContext || (window as any).webkitAudioContext)({ sampleRate: 16000 });
            outputAudioContextRef.current = new (window.AudioContext || (window as any).webkitAudioContext)({ sampleRate: 24000 });
            
            sessionPromiseRef.current = ai.live.connect({
                model: 'gemini-2.5-flash-native-audio-preview-09-2025',
                callbacks: {
                    onopen: () => {
                        if (!inputAudioContextRef.current || !mediaStreamRef.current) return;
                        setStatus('listening');

                        mediaStreamSourceRef.current = inputAudioContextRef.current.createMediaStreamSource(mediaStreamRef.current);
                        scriptProcessorRef.current = inputAudioContextRef.current.createScriptProcessor(4096, 1, 1);
                        
                        scriptProcessorRef.current.onaudioprocess = (audioProcessingEvent) => {
                            const inputData = audioProcessingEvent.inputBuffer.getChannelData(0);
                            const pcmBlob = createBlob(inputData);
                            sessionPromiseRef.current?.then((session) => {
                                session.sendRealtimeInput({ media: pcmBlob });
                            });
                        };
                        
                        mediaStreamSourceRef.current.connect(scriptProcessorRef.current);
                        scriptProcessorRef.current.connect(inputAudioContextRef.current.destination);
                    },
                    onmessage: async (message: LiveServerMessage) => {
                        const base64Audio = message.serverContent?.modelTurn?.parts[0]?.inlineData.data;
                        if (base64Audio && outputAudioContextRef.current) {
                            const outputCtx = outputAudioContextRef.current;
                            nextStartTimeRef.current = Math.max(nextStartTimeRef.current, outputCtx.currentTime);
                            const audioBuffer = await decodeAudioData(decode(base64Audio), outputCtx, 24000, 1);
                            const source = outputCtx.createBufferSource();
                            source.buffer = audioBuffer;
                            source.connect(outputCtx.destination);
                            source.addEventListener('ended', () => sourcesRef.current.delete(source));
                            source.start(nextStartTimeRef.current);
                            nextStartTimeRef.current += audioBuffer.duration;
                            sourcesRef.current.add(source);
                        }
                        if (message.serverContent?.interrupted) {
                            sourcesRef.current.forEach(source => source.stop());
                            sourcesRef.current.clear();
                            nextStartTimeRef.current = 0;
                        }
                    },
                    onerror: (e: ErrorEvent) => {
                        console.error("Live API Error:", e);
                        setError('An error occurred during the session.');
                        setStatus('error');
                        cleanup();
                    },
                    onclose: () => {
                        setStatus('idle');
                        cleanup();
                    },
                },
                config: {
                    responseModalities: [Modality.AUDIO],
                    speechConfig: { voiceConfig: { prebuiltVoiceConfig: { voiceName: 'Zephyr' } } },
                    systemInstruction: `You are an expert on Protopraxic Logic. Your agent identity is ${agentIdentity}. Keep your answers brief and conversational.`,
                },
            });
            await sessionPromiseRef.current;
        } catch (err) {
            console.error(err);
            setError('Failed to start session. Check microphone permissions.');
            setStatus('error');
            cleanup();
        }
    };

    const handleStop = async () => {
        try {
            const session = await sessionPromiseRef.current;
            session?.close();
        } catch (e) {
            console.error("Error closing session:", e);
        } finally {
            cleanup();
            setStatus('idle');
        }
    };

    useEffect(() => {
        return () => {
           handleStop();
        };
    }, []);

    if (!agentIdentity) {
        return (
            <div className="flex flex-col items-center justify-center bg-slate-800/30 rounded-xl border-2 border-dashed border-slate-700 shadow-lg p-8 min-h-[40vh] text-center">
                <div className="w-16 h-16 flex items-center justify-center bg-slate-700/50 rounded-full mb-4">
                    <ShieldExclamationIcon />
                </div>
                <h2 className="text-2xl font-bold text-white mb-2">Live Conversation Locked</h2>
                <p className="text-slate-400 max-w-md">
                    The agent must first establish its formal identity before engaging in live conversation. Please go to the <strong>PXL Simulator</strong> tab and complete the <strong>Agent Boot Sequence</strong>.
                </p>
            </div>
        );
    }

    const isConversationActive = status === 'listening' || status === 'connecting';

    return (
        <div className="flex flex-col items-center justify-center bg-slate-800/30 rounded-xl border border-slate-700/50 shadow-lg p-8 min-h-[40vh]">
            <h2 className="text-2xl font-bold text-white mb-2">Live Conversation</h2>
            <p className="text-slate-400 mb-6 text-center">Speak directly with a Gemini model trained on PXL.</p>

            <button
                onClick={isConversationActive ? handleStop : handleStart}
                disabled={status === 'connecting'}
                className="w-24 h-24 rounded-full flex items-center justify-center transition-all duration-300 ease-in-out disabled:opacity-50 disabled:cursor-wait focus:outline-none focus-visible:ring-4 focus-visible:ring-offset-4 focus-visible:ring-offset-slate-800"
                style={{
                  background: isConversationActive ? 'radial-gradient(circle, #f43f5e, #be123c)' : 'radial-gradient(circle, #22d3ee, #0891b2)',
                  boxShadow: `0 0 20px ${isConversationActive ? '#ef4444' : '#22d3ee'}`,
                }}
            >
                {isConversationActive ? <StopIcon /> : <MicrophoneIcon />}
            </button>
            
            <div className="mt-6 text-center h-12">
                <p className="text-lg font-semibold capitalize transition-opacity duration-300 text-cyan-400">
                    {status}
                </p>
                {error && <p className="text-red-400 mt-1">{error}</p>}
                 {status === 'listening' && (
                    <p className="text-slate-400 animate-pulse">Speak now...</p>
                )}
            </div>
        </div>
    );
};

export default Live;
